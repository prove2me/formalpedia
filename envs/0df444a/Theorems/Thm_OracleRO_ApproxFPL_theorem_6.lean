-- Prove2me | Theorems.Thm_OracleRO_ApproxFPL_theorem_6
-- name    : OracleRO.ApproxFPL.theorem_6
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T09:31:21.16273+00:00
-- url     : https://prove2.me/theorems/aeb8d710-a301-42e8-b914-3c4c176520e5
-- title:
--   Theorem 6 — Follow the Approximate Perturbed Leader has expected regret at most $2\sqrt{DRAT} + 2\epsilon T$
-- statement:
--   Let $\mathcal K\subseteq\mathbb R^n$ be a decision domain (not necessarily convex), $\epsilon>0$, and $M_\epsilon$ a measurable procedure that $\epsilon$-approximately maximizes linear functions over $\mathcal K$: $M_\epsilon(g)\in\mathcal K$ and $g\cdot M_\epsilon(g)\ge g\cdot x-\epsilon$ for all $g\in\mathbb R^n$, $x\in\mathcal K$. Let $T\ge1$ and let $f_1,\ldots,f_T\in\mathbb R^n$ be any fixed sequence of reward vectors. Let $D, R, A > 0$ satisfy, for all $x,y\in\mathcal K$ and $t=1,\ldots,T$:
--   1. $\|x-y\|_1\le D$ (an upper bound on the $\ell_1$ diameter of $\mathcal K$);
--   2. $|f_t\cdot x-f_t\cdot y|\le R$ (an upper bound on the variation of each reward over $\mathcal K$);
--   3. $\|f_t\|_1\le A$ (an upper bound on the $\ell_1$ norm of the rewards).
--
--   Let $x_1,\ldots,x_T$ be the decisions of Follow the Approximate Perturbed Leader (13) with $\eta=\sqrt{D/(RAT)}$: $x_t=M_\epsilon(f_{1:t-1}+p_t)$, where $f_{1:s}=\sum_{\tau\le s}f_\tau$ and $p_t$ is uniform on $[0,1/\eta]^n$. Then for every $x^*\in\mathcal K$,
--   $$
--   \sum_{t=1}^T f_t\cdot x^* \;-\; \mathbf E\Big[\sum_{t=1}^T f_t\cdot x_t\Big] \;\le\; 2\sqrt{DRAT}+2\epsilon T .
--   $$
--
--   Thus perturbed-leader online linear optimization tolerates an additive error $\epsilon$ in its linear optimization procedure at a cost of only $2\epsilon T$ in regret, and needs no convexity of $\mathcal K$. The paper uses this as the online-learning primitive for oracle-based robust optimization with linearly parametrized uncertainty.
--
--   **Formalization Note** The paper takes $R\ge\max_{t,x}|f_t\cdot x|$; the proof (Lemma 9, "they can differ by at most $R$") needs $R$ to bound the oscillation $|f_t\cdot x - f_t\cdot y|$ over $\mathcal K$, and with the printed reading the stability step fails (counterexample in Lemma 9's note). The printed hypothesis implies the one used here with $2R$ in place of $R$; for non-negative rewards they coincide. The maximum over $x^*$ is replaced by "for every $x^*\in\mathcal K$". The expectation is $\sum_t\int f_t\cdot M_\epsilon(f_{1:t-1}+p)\,d\mu_\eta(p)$, which by linearity equals $\mathbf E[\sum_t f_t\cdot x_t]$ for independent or shared perturbations. Measurability of $M_\epsilon$ makes the expectation a genuine integral (an approximate maximizer can always be chosen measurable). $D,R,A>0$ and $T\ge1$ make $\eta$ a well-defined positive number, as the formula $\eta = \sqrt{D/RAT}$ presupposes.
-- source:
--   Ben-Tal, Hazan, Koren, Mannor, Oracle-Based Robust Optimization via Online Learning, arXiv:1402.6361v1, p. 11, Theorem 6 (R read as an oscillation bound)

import Mathlib
import Definitions.Def_OracleRO_ApproxFPL_IsApproxLinOracle
import Definitions.Def_OracleRO_ApproxFPL_FPL

open MeasureTheory ProbabilityTheory

namespace OracleRO.ApproxFPL

/-- Theorem 6 (Ben-Tal, Hazan, Koren, Mannor, arXiv:1402.6361v1, p. 11): Follow the Approximate
Perturbed Leader (13) with an `ε`-approximate linear optimization procedure `M` over `K` and
parameter `η = √(D/(RAT))` has expected regret at most `2√(DRAT) + 2εT` against any fixed reward
sequence `f_1, …, f_T`: for every `x* ∈ K`,
`∑_{t=1}^T f_t · x* - E[∑_{t=1}^T f_t · x_t] ≤ 2√(DRAT) + 2εT`,
where `D` bounds the `ℓ₁` diameter of `K`, `A` bounds `‖f_t‖₁`, and `R` bounds the oscillation
`|f_t · x - f_t · y|` of each reward over `K`.

Formalization Note: the page assumes `R ≥ max_{t,x} |f_t · x|`; the proof (Lemma 9, "they can
differ by at most R") needs `R` to bound the oscillation, and the printed hypothesis gives this
with `2R`. `M` is assumed measurable so the expectation is a genuine integral; `D, R, A > 0` and
`T ≥ 1` make `η` a positive real. -/
theorem theorem_6 {n : ℕ} (K : Set (Fin n → ℝ)) (ε : ℝ) (hε : 0 < ε)
    (M : (Fin n → ℝ) → (Fin n → ℝ)) (hM : IsApproxLinOracle K ε M) (hMmeas : Measurable M)
    (f : ℕ → Fin n → ℝ) (T : ℕ) (hT : 1 ≤ T) (D R A : ℝ)
    (hD0 : 0 < D) (hR0 : 0 < R) (hA0 : 0 < A)
    (hD : ∀ x ∈ K, ∀ y ∈ K, ∑ i, |x i - y i| ≤ D)
    (hR : ∀ t ∈ Finset.Icc 1 T, ∀ x ∈ K, ∀ y ∈ K, |f t ⬝ᵥ x - f t ⬝ᵥ y| ≤ R)
    (hA : ∀ t ∈ Finset.Icc 1 T, ∑ i, |f t i| ≤ A) :
    ∀ xStar ∈ K, (∑ t ∈ Finset.Icc 1 T, f t ⬝ᵥ xStar) -
        fplExpectedReward M f (Real.sqrt (D / (R * A * T))) T ≤
      2 * Real.sqrt (D * R * A * T) + 2 * ε * T := by sorry

end OracleRO.ApproxFPL
