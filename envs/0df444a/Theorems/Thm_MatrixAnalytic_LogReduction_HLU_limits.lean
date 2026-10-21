-- Prove2me | Theorems.Thm_MatrixAnalytic_LogReduction_HLU_limits
-- name    : MatrixAnalytic.LogReduction.HLU_limits
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-20T15:46:08.887405+00:00
-- url     : https://prove2.me/theorems/5a608105-9730-4dab-aacb-3f7ecc550463
-- title:
--   Theorem 8.4.2 — limits of H^[k], L^[k], U^[k] for ergodic and transient QBDs
-- statement:
--   Let $\{X_t\}$ be an irreducible homogeneous QBD with transition matrix (8.1) and finitely many phases, and $H^{[k]}, L^{[k]}, U^{[k]}=H^{[k]}L^{[k]}+L^{[k]}H^{[k]}$ the matrices of the logarithmic reduction recursion (8.40)–(8.44). Let $G$ be the matrix of first passage probabilities from $\ell(1)$ to $\ell(0)$ and $\hat G$ the same matrix for the level-reversed QBD (8.25), in which $A_0$ and $A_2$ exchange roles.
--
--   If the QBD is ergodic (positive recurrent) and $g$ is the stationary probability vector of $G$, then, entrywise,
--   $$\lim_{k\to\infty}H^{[k]}=0,\qquad\lim_{k\to\infty}L^{[k]}=\mathbf 1\cdot g.$$
--   If the QBD is transient and $\hat g$ is the stationary probability vector of $\hat G$, then
--   $$\lim_{k\to\infty}H^{[k]}=\mathbf 1\cdot\hat g,\qquad\lim_{k\to\infty}L^{[k]}=0.$$
--   In both cases $\lim_{k\to\infty}U^{[k]}=0$. Here $\mathbf 1\cdot g$ is the matrix whose every row is $g$.
--
--   The theorem explains why the logarithmic reduction algorithm is numerically well behaved: the matrices $I-U^{[k]}$ to be inverted approach the identity.
--
--   **Formalization Note** The statement is restricted to finitely many phases: the proof uses $\lim_kG^k=\mathbf 1\cdot g$ and accumulation points of bounded sequences of matrices, and the page gives no meaning to "the stationary probability vector of $G$" for infinitely many phases. "The stationary probability vector" is formalized as a stationary probability vector that is the only one (uniqueness is a hypothesis, as the definite article presupposes). Ergodic is positive recurrence of every state (the book's index: "ergodicity, see positive recurrence"); transient is the failure of recurrence at every state. Limits are entrywise, in $[0,\infty]$. The boundary block of the level-reversed QBD is irrelevant to $\hat G$ and is taken to be $0$.
-- source:
--   Latouche & Ramaswami, Introduction to Matrix Analytic Methods in Stochastic Modeling, SIAM 1999, p. 194, Theorem 8.4.2

import Mathlib
import Definitions.Def_MatrixAnalytic_LogReduction_Chain
import Definitions.Def_MatrixAnalytic_LogReduction_QBD
import Definitions.Def_MatrixAnalytic_LogReduction_Passage

open scoped ENNReal

namespace MatrixAnalytic.LogReduction

open Filter Topology

/-- Theorem 8.4.2, p. 194, for finitely many phases. Let the QBD (8.1) be irreducible.
If it is ergodic (positive recurrent) and `g` is the stationary probability vector of `G` (8.3),
then `H^{[k]} → 0`, `L^{[k]} → 1·g` and `U^{[k]} = H^{[k]}L^{[k]} + L^{[k]}H^{[k]} → 0` entrywise
as `k → ∞`. If it is transient and `ĝ` is the stationary probability vector of `Ĝ`, the matrix
`G` of the level-reversed QBD (8.25), then `H^{[k]} → 1·ĝ`, `L^{[k]} → 0` and `U^{[k]} → 0`.
"The stationary probability vector" is read as: a stationary probability vector, and the only
one. -/
theorem HLU_limits {ι : Type*} [Fintype ι] [DecidableEq ι]
    (B A₀ A₁ A₂ : ι → ι → ℝ)
    (hP : IsStochasticC (qbdP B A₀ A₁ A₂))
    (hirr : IrreducibleC (qbdP B A₀ A₁ A₂)) :
    ((∀ x : ℕ × ι, PositiveRecurrent (qbdP B A₀ A₁ A₂) x) →
      ∀ g : ι → ℝ, IsStationaryVec (matG (qbdP B A₀ A₁ A₂)) g →
        (∀ g' : ι → ℝ, IsStationaryVec (matG (qbdP B A₀ A₁ A₂)) g' → g' = g) →
        (∀ i j : ι, Tendsto (fun k => logH A₀ A₁ A₂ k i j) atTop (𝓝 0)) ∧
        (∀ i j : ι, Tendsto (fun k => logL A₀ A₁ A₂ k i j) atTop (𝓝 (ENNReal.ofReal (g j)))) ∧
        (∀ i j : ι, Tendsto (fun k => logU A₀ A₁ A₂ k i j) atTop (𝓝 0))) ∧
    ((∀ x : ℕ × ι, ¬ Recurrent (qbdP B A₀ A₁ A₂) x) →
      ∀ ĝ : ι → ℝ, IsStationaryVec (matGhat A₀ A₁ A₂) ĝ →
        (∀ g' : ι → ℝ, IsStationaryVec (matGhat A₀ A₁ A₂) g' → g' = ĝ) →
        (∀ i j : ι, Tendsto (fun k => logH A₀ A₁ A₂ k i j) atTop (𝓝 (ENNReal.ofReal (ĝ j)))) ∧
        (∀ i j : ι, Tendsto (fun k => logL A₀ A₁ A₂ k i j) atTop (𝓝 0)) ∧
        (∀ i j : ι, Tendsto (fun k => logU A₀ A₁ A₂ k i j) atTop (𝓝 0))) := by sorry

end MatrixAnalytic.LogReduction
