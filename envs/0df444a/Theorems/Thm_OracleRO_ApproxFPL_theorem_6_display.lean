-- Prove2me | Theorems.Thm_OracleRO_ApproxFPL_theorem_6_display
-- name    : OracleRO.ApproxFPL.theorem_6_display
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T09:30:56.118183+00:00
-- url     : https://prove2.me/theorems/f5ebb37a-85c0-4263-99fe-7d41184d0d92
-- title:
--   §3.3, proof of Theorem 6 — expected reward of approximate FPL is at least $f_{1:T}\cdot x - D/\eta - \eta RAT - 2\epsilon T$ for every $\eta>0$
-- statement:
--   Let $\mathcal K\subseteq\mathbb R^n$, $\epsilon>0$, and $M_\epsilon$ a measurable $\epsilon$-approximate linear optimization procedure over $\mathcal K$. Let $T\ge 1$ and let $f_1,\ldots,f_T\in\mathbb R^n$ be fixed reward vectors. Let $D, R, A$ satisfy, for all $x,y\in\mathcal K$ and all $t = 1,\ldots,T$,
--   $$
--   \|x-y\|_1 \le D, \qquad |f_t\cdot x - f_t\cdot y| \le R, \qquad \|f_t\|_1\le A .
--   $$
--   Let $x_1,\ldots,x_T$ be the decisions of Follow the Approximate Perturbed Leader (13) with parameter $\eta>0$, that is $x_t = M_\epsilon(f_{1:t-1}+p_t)$ with $p_t$ uniform on $[0,1/\eta]^n$. Then for every $x\in\mathcal K$,
--   $$
--   \mathbf E\Big[\sum_{t=1}^T f_t\cdot x_t\Big] \;\ge\; f_{1:T}\cdot x - \frac{D}{\eta} - \eta RAT - 2\epsilon T .
--   $$
--
--   This is the regret bound for an arbitrary perturbation scale $\eta$; Theorem 6 is its specialization to the $\eta$ that balances $D/\eta$ against $\eta RAT$.
--
--   **Formalization Note** The page writes $\max_{x\in\mathcal K} f_{1:t}\cdot x$ with $t$ unbound; it means $f_{1:T}$, and the maximum is replaced by "for every $x\in\mathcal K$". As in Lemma 9, $R$ bounds the oscillation of each $f_t$ over $\mathcal K$ rather than $|f_t\cdot x|$ (the printed hypothesis implies this with $2R$). The expectation is $\sum_{t}\int f_t\cdot M_\epsilon(f_{1:t-1}+p)\,d\mu_\eta(p)$, by linearity of expectation. The bound is stated for $T\ge 1$; the paper's proof goes through Lemma 8, which assumes $T\ge2$, and the case $T=1$ also holds.
-- source:
--   Ben-Tal, Hazan, Koren, Mannor, Oracle-Based Robust Optimization via Online Learning, arXiv:1402.6361v1, §3.3, proof of Theorem 6, display, p. 13

import Mathlib
import Definitions.Def_OracleRO_ApproxFPL_IsApproxLinOracle
import Definitions.Def_OracleRO_ApproxFPL_FPL

open MeasureTheory ProbabilityTheory

namespace OracleRO.ApproxFPL

/-- The bound for a general `η > 0` displayed in the proof of Theorem 6 (arXiv:1402.6361v1, §3.3,
p. 13): for every `x ∈ K`, the expected total reward of (13) satisfies
`E[∑_{t=1}^T f_t · x_t] ≥ f_{1:T} · x - D/η - ηRAT - 2εT`,
with `R` a bound on the oscillation `|f_t · x - f_t · y|` over `x, y ∈ K`, `A` a bound on
`‖f_t‖₁` and `D` a bound on the `ℓ₁` diameter of `K`. -/
theorem theorem_6_display {n : ℕ} (K : Set (Fin n → ℝ)) (ε : ℝ) (hε : 0 < ε)
    (M : (Fin n → ℝ) → (Fin n → ℝ)) (hM : IsApproxLinOracle K ε M) (hMmeas : Measurable M)
    (f : ℕ → Fin n → ℝ) (T : ℕ) (hT : 1 ≤ T) (D R A : ℝ)
    (hD : ∀ x ∈ K, ∀ y ∈ K, ∑ i, |x i - y i| ≤ D)
    (hR : ∀ t ∈ Finset.Icc 1 T, ∀ x ∈ K, ∀ y ∈ K, |f t ⬝ᵥ x - f t ⬝ᵥ y| ≤ R)
    (hA : ∀ t ∈ Finset.Icc 1 T, ∑ i, |f t i| ≤ A)
    (η : ℝ) (hη : 0 < η) :
    ∀ x ∈ K, prefixSum f T ⬝ᵥ x - D / η - η * R * A * T - 2 * ε * T ≤
      fplExpectedReward M f η T := by sorry

end OracleRO.ApproxFPL
