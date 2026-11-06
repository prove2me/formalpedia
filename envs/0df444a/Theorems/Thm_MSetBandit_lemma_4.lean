-- Prove2me | Theorems.Thm_MSetBandit_lemma_4
-- name    : MSetBandit.lemma_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T00:44:46.171666+00:00
-- url     : https://prove2.me/theorems/5f12b831-8ec2-4031-bce3-013196ecbf5f
-- title:
--   Lemma 4 — exponential-weights bound with approximate projections
-- statement:
--   Fix integers $d\ge 2$ and $1\le m\le d-1$. Let $T\ge1$ and $\delta\in(0,1)$, let $\eta$ be the learning rate of Algorithm 1 and $\lambda=128\eta d$. Along every sample path of Algorithm 1, with $p_t=p_{\theta_t}$ and surrogate losses $Z_t(x)=x^\top\hat\ell_t-\eta c_t^\top x$, for every distribution $q\in\mathcal P_\lambda$,
--   $$
--   \sum_{t=1}^T\Big(\mathbb E_{X\sim p_t}[Z_t(X)]-\mathbb E_{X\sim q}[Z_t(X)]\Big)\le\frac{\mathrm{KL}(q\,\|\,p_1)}{\eta}+1+2\eta\sum_{t=1}^T\mathbb E_{X\sim p_t}\big[Z_t(X)^2\big].
--   $$
--
--   The constant $1$ is the accumulated projection error $T\varepsilon_{\mathrm p}/\eta$. Applied with the smoothed comparators $q_x$ it gives the first term of the regret decomposition in the proof of Theorem 1.
--
--   Differences from the source:
--   - encoding: rounds $t=1,\dots,T$ → rounds indexed $0,\dots,T-1$; reason: Lean convention; same instances
--   - encoding: items $1,\dots,d$ → items $0,\dots,d-1$ (`Fin d`); reason: Lean convention; same instances
--   - encoding: actions $x\in\{0,1\}^d$ with $\|x\|_1=m$ → $m$-element subsets of `Fin d` (`Action d m`) with indicator vector `ind`; reason: the page identifies actions with $m$-sets (p.3); same instances
--   - encoding: "When running Algorithm 1" → every realized sequence $(\ell_t,\theta_t,X_t)$ satisfying `IsAlgPath`; reason: the claim is deterministic given the realized sequence; every realization of the run is such a sequence
--   - encoding: $\mathrm{KL}(p\|q)$ with $+\infty$ when $p(x)>0=q(x)$ → the finite sum $\sum_xp(x)\log(p(x)/q(x))$ (`ConvexRMDP.kl`); reason: every second argument is a weighted $m$-set distribution or $U$, which has full support, so the values agree
--   - generalization: line 11 runs the ellipsoid procedure of Appendix D.1 for a predetermined number of iterations "with a sufficiently large constant" → $\theta_{t+1}$ is any vector with $\theta_{t+1}-\tilde\theta_{t+1}\in\mathcal D_{\mathrm p}$ satisfying (65) whenever $\mathrm{KL}(U\|p_{\tilde\theta_{t+1}})\le T$; reason: the paper's procedure outputs such a vector (Lemma 8) and the proofs use only (65); the statement specializes to the paper's run
-- source:
--   Bacchiocchi–Cesari–Colomboni, An Efficient Minimax-Optimal Algorithm for Adversarial m-Set Bandits, arXiv:2608.12231, Appendix C, Lemma 4, p.26

import Mathlib
import Definitions.Def_ConvexRMDP_kl
import Definitions.Def_MSetBandit_Plam
import Definitions.Def_MSetBandit_IsAlgPath
import Definitions.Def_MSetBandit_surrogate
import Definitions.Def_MSetBandit_expect
open Matrix

namespace MSetBandit

/-- **Lemma 4** (Bacchiocchi–Cesari–Colomboni, *An Efficient Minimax-Optimal Algorithm for Adversarial m-Set Bandits*, arXiv:2608.12231, Appendix C, p.26). When running Algorithm 1, for every distribution
`q ∈ P_λ`,
`Σ_{t=1}^T (E_{X∼p_t}[Z_t(X)] − E_{X∼q}[Z_t(X)]) ≤ KL(q ‖ p₁)/η + 1 + 2η Σ_{t=1}^T E_{X∼p_t}[Z_t(X)²]`,
where `p_t = p_{θ_t}`, `Z_t(x) = x^⊤ℓ̂_t − η c_t^⊤x`, `η` is the learning rate and `λ = 128ηd`.

Stated on every sample path of Algorithm 1 (`IsAlgPath`), with `T ≥ 1`, `δ ∈ (0, 1)`,
`1 ≤ m ≤ d − 1`.

**Formalization Note.** Rounds are 0-based: the sum runs over `t < T` and `p₁` is `p_{θ 0}`.
`KL` is `ConvexRMDP.kl`; its second argument has full support. -/
theorem lemma_4 {d m : ℕ} (hm : 1 ≤ m) (hmd : m + 1 ≤ d) {T : ℕ} (hT : 1 ≤ T) {δ : ℝ}
    (hδ0 : 0 < δ) (hδ1 : δ < 1) (ℓ θ : ℕ → Fin d → ℝ) (X : ℕ → Action d m)
    (hpath : IsAlgPath d m T δ ℓ θ X) :
    ∀ q ∈ Plam (d := d) (m := m) (128 * etaAlg d m T δ * d),
      ∑ t ∈ Finset.range T,
          (expect (wdist (θ t)) (surrogate (etaAlg d m T δ) (θ t) (X t) (ind (X t) ⬝ᵥ ℓ t)) -
            expect q (surrogate (etaAlg d m T δ) (θ t) (X t) (ind (X t) ⬝ᵥ ℓ t))) ≤
        ConvexRMDP.kl q (wdist (θ 0)) / etaAlg d m T δ + 1 +
          2 * etaAlg d m T δ * ∑ t ∈ Finset.range T,
            expect (wdist (θ t))
              (fun x => surrogate (etaAlg d m T δ) (θ t) (X t) (ind (X t) ⬝ᵥ ℓ t) x ^ 2) := by sorry

end MSetBandit
