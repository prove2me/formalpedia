-- Prove2me | Theorems.Thm_MSetBandit_proposition_1
-- name    : MSetBandit.proposition_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T00:45:48.976686+00:00
-- url     : https://prove2.me/theorems/d6de6c14-478e-47c7-8980-f075816abb42
-- title:
--   Proposition 1 (first sentence) — every $p_{t+1}$ lies in $\mathcal P_{\lambda/2}$ and satisfies (17)
-- statement:
--   Fix integers $d\ge 2$ and $1\le m\le d-1$. Let $T\ge1$ and $\delta\in(0,1)$, let $\eta$ be the learning rate of Algorithm 1, $\lambda=128\eta d$ and $\varepsilon_{\mathrm p}=\eta/T$. Along every sample path of Algorithm 1, for every round $t\in[T]$ the next sampling distribution $p_{t+1}=p_{\theta_{t+1}}$ is a weighted $m$-set distribution in $\mathcal P_{\lambda/2}$, and $\theta_{t+1}$ satisfies (17) at round $t$: for every $q\in\mathcal P_\lambda$,
--   $$
--   \mathrm{KL}(q\,\|\,p_{t+1})+\mathrm{KL}(p_{t+1}\,\|\,\tilde p_{t+1})\le\mathrm{KL}(q\,\|\,\tilde p_{t+1})+\varepsilon_{\mathrm p},
--   $$
--   where $\tilde p_{t+1}=p_{\tilde\theta_{t+1}}$ and $\tilde\theta_{t+1}=\theta_t-\eta z_t$ is the unprojected multiplicative-weights parameter.
--
--   In the paper's indexing this is the statement for every $t\in\{2,\dots,T+1\}$: $p_t\in\mathcal P_{\lambda/2}$ and (17) holds at round $t-1$. It guarantees that Lemmas 1 and 3 apply at every round and supplies the approximate projection inequality used in Lemma 4.
--
--   Differences from the source:
--   - encoding: rounds $t=1,\dots,T$ → rounds indexed $0,\dots,T-1$; reason: Lean convention; same instances
--   - encoding: items $1,\dots,d$ → items $0,\dots,d-1$ (`Fin d`); reason: Lean convention; same instances
--   - encoding: actions $x\in\{0,1\}^d$ with $\|x\|_1=m$ → $m$-element subsets of `Fin d` (`Action d m`) with indicator vector `ind`; reason: the page identifies actions with $m$-sets (p.3); same instances
--   - encoding: "When running Algorithm 1" → every realized sequence $(\ell_t,\theta_t,X_t)$ satisfying `IsAlgPath`; reason: the claim is deterministic given the realized sequence; every realization of the run is such a sequence
--   - encoding: $\mathrm{KL}(p\|q)$ with $+\infty$ when $p(x)>0=q(x)$ → the finite sum $\sum_xp(x)\log(p(x)/q(x))$ (`ConvexRMDP.kl`); reason: every second argument is a weighted $m$-set distribution or $U$, which has full support, so the values agree
--   - generalization: line 11 runs the ellipsoid procedure of Appendix D.1 for a predetermined number of iterations "with a sufficiently large constant" → $\theta_{t+1}$ is any vector with $\theta_{t+1}-\tilde\theta_{t+1}\in\mathcal D_{\mathrm p}$ satisfying (65) whenever $\mathrm{KL}(U\|p_{\tilde\theta_{t+1}})\le T$; reason: the paper's procedure outputs such a vector (Lemma 8) and the proofs use only (65); the statement specializes to the paper's run
-- source:
--   Bacchiocchi–Cesari–Colomboni, An Efficient Minimax-Optimal Algorithm for Adversarial m-Set Bandits, arXiv:2608.12231, Section 5.3, Proposition 1 (first sentence), p.14 (restated p.39)

import Mathlib
import Definitions.Def_ConvexRMDP_kl
import Definitions.Def_MSetBandit_Plam
import Definitions.Def_MSetBandit_IsAlgPath
open Matrix

namespace MSetBandit

/-- **Proposition 1, first sentence** (Bacchiocchi–Cesari–Colomboni, *An Efficient Minimax-Optimal Algorithm for Adversarial m-Set Bandits*, arXiv:2608.12231, Section 5.3, p.14; restated p.39). For every
`t ∈ {2, …, T + 1}`, Algorithm 1 maintains a weighted m-set distribution `p_t = p_{θ_t} ∈ P_{λ/2}`,
represented by `θ_t ∈ ℝ^d` satisfying (17) at round `t − 1`:
`KL(q ‖ p_t) + KL(p_t ‖ p̃_t) ≤ KL(q ‖ p̃_t) + ε_p` for every `q ∈ P_λ`, where `p̃_t = p_{θ̃_t}`,
`ε_p = η/T`, `λ = 128ηd`.

Stated on every sample path of Algorithm 1 (`IsAlgPath`), with `T ≥ 1`, `δ ∈ (0, 1)`,
`1 ≤ m ≤ d − 1`.

**Formalization Note.** Rounds are 0-based: the paper's `θ_{t+1}` for `t ∈ [T]` is `θ (t+1)` for
`t < T`, and `θ̃_{t+1} = mwuParam η (θ t) (X t) (Y t)` with `Y t = X_t^⊤ℓ_t`. The second sentence
of Proposition 1 (running time and space in the arithmetic model) is not part of this statement.
`KL` is `ConvexRMDP.kl`; its second arguments have full support. -/
theorem proposition_1 {d m : ℕ} (hm : 1 ≤ m) (hmd : m + 1 ≤ d) {T : ℕ} (hT : 1 ≤ T) {δ : ℝ}
    (hδ0 : 0 < δ) (hδ1 : δ < 1) (ℓ θ : ℕ → Fin d → ℝ) (X : ℕ → Action d m)
    (hpath : IsAlgPath d m T δ ℓ θ X) :
    ∀ t < T,
      wdist (m := m) (θ (t + 1)) ∈ Plam (128 * etaAlg d m T δ * d / 2) ∧
      ∀ q ∈ Plam (d := d) (m := m) (128 * etaAlg d m T δ * d),
        ConvexRMDP.kl q (wdist (θ (t + 1))) +
            ConvexRMDP.kl (wdist (m := m) (θ (t + 1)))
              (wdist (mwuParam (etaAlg d m T δ) (θ t) (X t) (ind (X t) ⬝ᵥ ℓ t))) ≤
          ConvexRMDP.kl q (wdist (mwuParam (etaAlg d m T δ) (θ t) (X t) (ind (X t) ⬝ᵥ ℓ t))) +
            etaAlg d m T δ / T := by sorry

end MSetBandit
