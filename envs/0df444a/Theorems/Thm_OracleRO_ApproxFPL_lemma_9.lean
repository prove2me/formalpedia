-- Prove2me | Theorems.Thm_OracleRO_ApproxFPL_lemma_9
-- name    : OracleRO.ApproxFPL.lemma_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T09:30:45.879785+00:00
-- url     : https://prove2.me/theorems/45ac3650-3fd5-4fa9-ae83-6ad4c2a2105c
-- title:
--   Lemma 9 — stability of the approximate perturbed leader, $\ge -\eta RA$ (R an oscillation bound)
-- statement:
--   Let $\mathcal K \subseteq \mathbb R^n$, $\epsilon > 0$, and $M_\epsilon$ a measurable $\epsilon$-approximate linear optimization procedure over $\mathcal K$. Let $\eta > 0$, $t \ge 1$, and reward vectors $f_1,\ldots,f_t \in \mathbb R^n$, with $f_{1:s} = \sum_{\tau=1}^s f_\tau$. Suppose
--   1. $|f_t\cdot x - f_t\cdot y| \le R$ for all $x, y\in\mathcal K$ (the reward $f_t$ varies by at most $R$ over $\mathcal K$), and
--   2. $\|f_t\|_1 = \sum_i |(f_t)_i| \le A$.
--
--   If $p$ is distributed uniformly in the cube $[0,1/\eta]^n$, then
--   $$
--   \mathbf E\big[M_\epsilon(f_{1:t-1} + p)\cdot f_t\big] - \mathbf E\big[M_\epsilon(f_{1:t} + p)\cdot f_t\big] \;\ge\; -\eta R A .
--   $$
--
--   The lemma measures how much the real algorithm, which must decide before seeing $f_t$, loses against the hypothetical one that sees it: shifting the uniform perturbation by $f_t$ changes the distribution of the decision only on a fraction at most $\eta\|f_t\|_1$ of the cube.
--
--   **Formalization Note** The paper assumes $R \ge \max_{t,x}|f_t\cdot x|$, a bound on the magnitude of the rewards. Under that reading the printed inequality is false: for $\mathcal K = \{-1,1\}\subset\mathbb R$, $M_\epsilon$ the exact maximizer (the sign), $f_{1:t-1} = -A$, $f_t = A = R$ and $\eta A\le 1$, the left side equals $-2\eta RA$. The proof's step "they can differ by at most $R$" needs $R$ to bound the oscillation $|f_t\cdot x - f_t\cdot y|$ over $\mathcal K$, which is the hypothesis stated here; the printed hypothesis implies it with $2R$ in place of $R$, and for non-negative rewards (Kalai–Vempala's setting) the two coincide. Only $f_t$ is constrained, which is weaker than the paper's bound over all $t$. Measurability of $M_\epsilon$ makes the expectations genuine integrals; an approximate maximizer can always be chosen measurable.
-- source:
--   Ben-Tal, Hazan, Koren, Mannor, Oracle-Based Robust Optimization via Online Learning, arXiv:1402.6361v1, p. 13, Lemma 9 (R read as an oscillation bound)

import Mathlib
import Definitions.Def_OracleRO_ApproxFPL_IsApproxLinOracle
import Definitions.Def_OracleRO_ApproxFPL_FPL

open MeasureTheory ProbabilityTheory

namespace OracleRO.ApproxFPL

/-- Lemma 9 (arXiv:1402.6361v1, p. 13), with `R` read as a bound on the oscillation of the reward
`f_t` over `K`: for `p` uniform on `[0, 1/η]ⁿ`,
`E[M(f_{1:t-1} + p) · f_t] - E[M(f_{1:t} + p) · f_t] ≥ -ηRA`,
whenever `|f_t · x - f_t · y| ≤ R` for all `x, y ∈ K` and `‖f_t‖₁ ≤ A`.

Formalization Note: the page assumes `R ≥ max_{t,x} |f_t · x|`; under that reading the lemma is
false (`K = {-1, 1} ⊂ ℝ`, `M` = sign, `f_{1:t-1} = -A`, `f_t = A = R`, `ηA ≤ 1` gives `-2ηRA`).
The printed hypothesis implies the oscillation bound with `2R` in place of `R`. `M` is assumed
measurable so that the expectations are genuine integrals. -/
theorem lemma_9 {n : ℕ} (K : Set (Fin n → ℝ)) (ε : ℝ) (hε : 0 < ε)
    (M : (Fin n → ℝ) → (Fin n → ℝ)) (hM : IsApproxLinOracle K ε M) (hMmeas : Measurable M)
    (η : ℝ) (hη : 0 < η) (R A : ℝ) (f : ℕ → Fin n → ℝ) (t : ℕ) (ht : 1 ≤ t)
    (hR : ∀ x ∈ K, ∀ y ∈ K, |f t ⬝ᵥ x - f t ⬝ᵥ y| ≤ R)
    (hA : ∑ i, |f t i| ≤ A) :
    -(η * R * A) ≤
      (∫ p, M (prefixSum f (t - 1) + p) ⬝ᵥ f t ∂(perturbLaw n η)) -
        ∫ p, M (prefixSum f t + p) ⬝ᵥ f t ∂(perturbLaw n η) := by sorry

end OracleRO.ApproxFPL
