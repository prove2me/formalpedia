-- Prove2me | Theorems.Thm_MSetBandit_lemma_1
-- name    : MSetBandit.lemma_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T00:42:56.246966+00:00
-- url     : https://prove2.me/theorems/c66e6f88-e244-46fc-a590-2f77f582dc38
-- title:
--   Lemma 1 — affine upper bound $x^\top M^{-1}x\le\phi_p(x)=c_p^\top x/4$ on the leverage score
-- statement:
--   Fix integers $d\ge 2$ and $1\le m\le d-1$. Let $\lambda\in(0,1)$ and let $p=p_\theta\in\mathcal P_\lambda$ be a weighted $m$-set distribution with marginal vector $\mu$ and second-moment matrix $M$. For $x\in\mathcal X$ let $\phi_p(x)=1+\sum_{i=1}^d(x_i-\mu_i)^2/(\mu_i(1-\mu_i))$ and let $c_p$ be the vector of (13). Then:
--   1. for every $x\in\mathcal X$, $\;x^\top M^{-1}x\le\phi_p(x)$;
--   2. for every $x\in\mathcal X$, $\;4\phi_p(x)=c_p^\top x$;
--   3. $\mathbb E_{X\sim p}[\phi_p(X)]=d+1$;
--   4. for every $x\in\mathcal X$,
--   $$
--   0\le\phi_p(x)\le1+\frac{2d}{\lambda}.
--   $$
--
--   The bound replaces the quadratic leverage score in the surrogate loss of Zimmert and Lattimore by a function that is linear in the action, which keeps the exponential-weights update inside the weighted $m$-set family.
--
--   Differences from the source:
--   - encoding: items $1,\dots,d$ → items $0,\dots,d-1$ (`Fin d`); reason: Lean convention; same instances
--   - encoding: actions $x\in\{0,1\}^d$ with $\|x\|_1=m$ → $m$-element subsets of `Fin d` (`Action d m`) with indicator vector `ind`; reason: the page identifies actions with $m$-sets (p.3); same instances
-- source:
--   Bacchiocchi–Cesari–Colomboni, An Efficient Minimax-Optimal Algorithm for Adversarial m-Set Bandits, arXiv:2608.12231, Section 5.1, Lemma 1, p.11 (restated p.25)

import Mathlib
import Definitions.Def_MSetBandit_Plam
import Definitions.Def_MSetBandit_wdist
import Definitions.Def_MSetBandit_phi
import Definitions.Def_MSetBandit_cvec
import Definitions.Def_MSetBandit_expect
import Definitions.Def_MSetBandit_secondMoment
open Matrix

namespace MSetBandit

/-- **Lemma 1** (Bacchiocchi–Cesari–Colomboni, *An Efficient Minimax-Optimal Algorithm for Adversarial m-Set Bandits*, arXiv:2608.12231, Section 5.1, p.11; restated p.25). Let `p ∈ P_λ` be a weighted m-set
distribution, where `1 ≤ m ≤ d − 1`, and let `µ, M` be its marginal vector and second-moment
matrix. Then:
1. for every `x ∈ X`, `x^⊤M⁻¹x ≤ ϕ_p(x)`;
2. `4ϕ_p(x) = c_p^⊤x` for every `x ∈ X`, with `c_p` as in (13);
3. `E_{X∼p}[ϕ_p(X)] = d + 1`;
4. for every `x ∈ X`, `0 ≤ ϕ_p(x) ≤ 1 + 2d/λ`.

**Formalization Note.** `λ ∈ (0, 1)` as fixed in Section 2 (p.4); `p = p_θ`. -/
theorem lemma_1 {d m : ℕ} (hm : 1 ≤ m) (hmd : m + 1 ≤ d) {lam : ℝ} (hlam0 : 0 < lam)
    (hlam1 : lam < 1) (θ : Fin d → ℝ) (hp : wdist (m := m) θ ∈ Plam lam) :
    (∀ x : Action d m,
      ind x ⬝ᵥ ((secondMoment (wdist (m := m) θ))⁻¹ *ᵥ ind x) ≤ phi (wdist θ) x) ∧
    (∀ x : Action d m, 4 * phi (wdist θ) x = cvec (wdist (m := m) θ) ⬝ᵥ ind x) ∧
    expect (wdist θ) (phi (wdist (m := m) θ)) = (d : ℝ) + 1 ∧
    (∀ x : Action d m, 0 ≤ phi (wdist θ) x ∧ phi (wdist θ) x ≤ 1 + 2 * (d : ℝ) / lam) := by sorry

end MSetBandit
