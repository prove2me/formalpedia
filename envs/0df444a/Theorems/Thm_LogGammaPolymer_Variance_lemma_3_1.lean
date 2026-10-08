-- Prove2me | Theorems.Thm_LogGammaPolymer_Variance_lemma_3_1
-- name    : LogGammaPolymer.Variance.lemma_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T14:22:51.013777+00:00
-- url     : https://prove2.me/theorems/9b182426-d134-435c-9944-6405568c9e70
-- title:
--   Lemma 3.1 — monotonicity of the recursion (3.2) in the boundary values
-- statement:
--   Let $\{U_{i,0},V_{0,j},Y_{i,j}: i,j\in\mathbb N\}$ and $\{\widetilde U_{i,0},\widetilde V_{0,j},\widetilde Y_{i,j}: i,j\in\mathbb N\}$ be two families of positive initial values with
--   $$U_{i,0}\ge\widetilde U_{i,0},\qquad V_{0,j}\le\widetilde V_{0,j},\qquad Y_{i,j}=\widetilde Y_{i,j}\qquad(i,j\in\mathbb N).$$
--   Define $\{U_{i,j},V_{i,j}\}$ and $\{\widetilde U_{i,j},\widetilde V_{i,j}\}$ on $\mathbb N^2$ by the recursion (3.2). Then
--   $$U_{i,j}\ge\widetilde U_{i,j}\quad\text{and}\quad V_{i,j}\le\widetilde V_{i,j}\qquad\text{for all }(i,j)\in\mathbb N^2.$$
--
--   Raising the horizontal boundary and lowering the vertical one propagates through the whole quadrant. This comparison is the engine behind the partition-function comparison of Lemma 5.1.
--
--   **Formalization Note** Each family is a function on $\mathbb Z_+^2$, positive off the (unused) origin.
-- source:
--   Seppäläinen, Scaling for a one-dimensional directed polymer with boundary conditions, arXiv:0911.2446v4, Lemma 3.1, p. 11

import Mathlib
import Definitions.Def_LogGammaPolymer_Variance_Paths
import Definitions.Def_LogGammaPolymer_Variance_Environment
open MeasureTheory ProbabilityTheory

namespace LogGammaPolymer.Variance

theorem lemma_3_1 (Y Yt : ℕ × ℕ → ℝ)
    (hY : ∀ p : ℕ × ℕ, p ≠ (0, 0) → 0 < Y p) (hYt : ∀ p : ℕ × ℕ, p ≠ (0, 0) → 0 < Yt p)
    (hU : ∀ i : ℕ, 1 ≤ i → Yt (i, 0) ≤ Y (i, 0))
    (hV : ∀ j : ℕ, 1 ≤ j → Y (0, j) ≤ Yt (0, j))
    (hbulk : ∀ i j : ℕ, 1 ≤ i → 1 ≤ j → Y (i, j) = Yt (i, j)) :
    ∀ i j : ℕ, 1 ≤ i → 1 ≤ j → U Yt i j ≤ U Y i j ∧ V Y i j ≤ V Yt i j := by sorry

end LogGammaPolymer.Variance
