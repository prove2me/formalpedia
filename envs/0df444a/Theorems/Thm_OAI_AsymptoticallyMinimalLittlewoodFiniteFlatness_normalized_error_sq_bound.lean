-- Prove2me | Theorems.Thm_OAI_AsymptoticallyMinimalLittlewoodFiniteFlatness_normalized_error_sq_bound
-- name    : OAI.AsymptoticallyMinimalLittlewoodFiniteFlatness.normalized_error_sq_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T09:39:40.476418+00:00
-- url     : https://prove2.me/theorems/d5d1dc1c-9ba4-47e1-9f46-c4f4ad54cf23
-- title:
--   An upper bound on the modulus forces small mean-square error
-- statement:
--   Let $N\ge1$, $\eta>0$, and let $f_N(t)=|P_{\varepsilon_N}(t)|/\sqrt N$ be the normalized modulus of the chosen sign polynomial. If $f_N\le1+\eta$ everywhere on $\mathbb{R}/\mathbb{Z}$, then
--   $$
--   \int_{\mathbb{R}/\mathbb{Z}}\bigl(f_N(t)-1\bigr)^2dt\le2\eta .
--   $$
--
--   Since $\int f_N^2=1$, a uniform upper bound close to $1$ forces $f_N$ to be close to $1$ in mean square. No $p$-dependent choice of signs is needed.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Littlewood/MinimizingFamily.lean#L162-L200

import Mathlib
import Definitions.Def_LittlewoodFiniteFlatness
import Definitions.Def_OAI_Analysis_Littlewood_MinimizingFamily

open OAI OAI.AsymptoticallyMinimalLittlewoodFiniteFlatness
open MeasureTheory Filter Complex
open scoped BigOperators Topology ComplexConjugate
variable (hmain : ∀ η : ℝ, 0 < η → ∃ N₀ : ℕ, 1 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
  ∃ ε : Fin N → ℝ, IsRealSigning ε ∧
    ∀ z : ℂ, ‖z‖ = 1 → ‖littlewoodValue ε z‖ ≤ (1 + η) * Real.sqrt N)

theorem OAI.AsymptoticallyMinimalLittlewoodFiniteFlatness.normalized_error_sq_bound {N : ℕ} (hN : 1 ≤ N) {η : ℝ} (hη : 0 < η)
    (hb : ∀ t, normalized N t ≤ 1 + η) :
    (∫ t : UnitAddCircle, (normalized N t - 1) ^ 2 ∂μ) ≤ 2 * η := by sorry
