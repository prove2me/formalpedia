-- Prove2me | Theorems.Thm_OAI_AsymptoticallyMinimalLittlewoodFiniteFlatness_circlePolynomial_energy
-- name    : OAI.AsymptoticallyMinimalLittlewoodFiniteFlatness.circlePolynomial_energy
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T09:39:03.597175+00:00
-- url     : https://prove2.me/theorems/1e7343f4-05eb-47be-a580-c9117f3c6057
-- title:
--   Parseval for a finite trigonometric polynomial
-- statement:
--   For real coefficients $\varepsilon_0,\dots,\varepsilon_{N-1}$, the polynomial $P(t)=\sum_k\varepsilon_ke^{2\pi ikt}$ on $\mathbb{R}/\mathbb{Z}$ satisfies
--   $$
--   \int_{\mathbb{R}/\mathbb{Z}}|P(t)|^2\,dt=\sum_{k=0}^{N-1}\varepsilon_k^2 .
--   $$
--
--   For a sign polynomial the mean square modulus is exactly $N$, so the normalized modulus $|P|/\sqrt N$ has second moment $1$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Littlewood/MinimizingFamily.lean#L94-L116

import Mathlib
import Definitions.Def_LittlewoodFiniteFlatness
import Definitions.Def_OAI_Analysis_Littlewood_MinimizingFamily

open OAI OAI.AsymptoticallyMinimalLittlewoodFiniteFlatness
open MeasureTheory Filter Complex
open scoped BigOperators Topology ComplexConjugate
variable (hmain : ∀ η : ℝ, 0 < η → ∃ N₀ : ℕ, 1 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
  ∃ ε : Fin N → ℝ, IsRealSigning ε ∧
    ∀ z : ℂ, ‖z‖ = 1 → ‖littlewoodValue ε z‖ ≤ (1 + η) * Real.sqrt N)

theorem OAI.AsymptoticallyMinimalLittlewoodFiniteFlatness.circlePolynomial_energy {N : ℕ} (ε : Fin N → ℝ) :
    (∫ t : UnitAddCircle, ‖circlePolynomial ε t‖ ^ 2 ∂μ) = ∑ k, (ε k) ^ 2 := by sorry
