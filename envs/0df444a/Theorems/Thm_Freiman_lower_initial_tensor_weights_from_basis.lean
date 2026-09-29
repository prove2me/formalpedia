-- Prove2me | Theorems.Thm_Freiman_lower_initial_tensor_weights_from_basis
-- name    : Freiman.lower_initial_tensor_weights_from_basis
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T12:18:15.4818+00:00
-- url     : https://prove2.me/theorems/24089ebc-1e57-4ed6-ad7c-72430d5b0051
-- title:
--   Freiman lower construction: initial tensor weights from basis
-- statement:
--   Products of three nonnegative source Bernstein bases form a partition of unity.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), parts/lower_core.tex, prop:lc-H-contacts; exact initial contact appendix

import Definitions.Def_Freiman_lowerInitialSeamData
import Definitions.Def_Freiman_lowerInitialNData
import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman

open scoped BigOperators

theorem Freiman.lower_initial_tensor_weights_from_basis (x y z : ℝ)
    (hx : (∀ i : Fin 3, 0 ≤ certBernsteinBasis i (85*x)) ∧ (∑ i : Fin 3, certBernsteinBasis i (85*x))=1)
    (hy : (∀ i : Fin 3, 0 ≤ certBernsteinBasis i (3*y)) ∧ (∑ i : Fin 3, certBernsteinBasis i (3*y))=1)
    (hz : (∀ i : Fin 3, 0 ≤ certBernsteinBasis i (3*z)) ∧ (∑ i : Fin 3, certBernsteinBasis i (3*z))=1) :
    (∀ i j k : Fin 3, 0 ≤ lowerInitialWeight x y z i j k) ∧
    (∑ i : Fin 3, ∑ j : Fin 3, ∑ k : Fin 3, lowerInitialWeight x y z i j k)=1 := by
  sorry
