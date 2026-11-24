-- Prove2me | Theorems.Thm_GlobalTheory_cayleyInv_one_sub
-- name    : GlobalTheory.cayleyInv_one_sub
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:53:28.755137+00:00
-- url     : https://prove2.me/theorems/42466d27-07b5-4e31-a577-83bde9e26656
-- title:
--   Global Theory: cayley Inv one sub
-- statement:
--   The Global Theory construction uses the cayley Inv one sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/UnitaryFamilyEqCayleyOfSkewFamily.lean#L8-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/UnitaryFamilyEqCayleyOfSkewFamily.lean#L8-L14

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_UnitaryFamilyEqCayleyOfSkewFamily
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix
open GlobalTheory
variable {n : ℕ}

theorem GlobalTheory.cayleyInv_one_sub (X : Matrix (Fin n) (Fin n) ℂ) (hu : IsUnit (X + 1).det) :
    1 - (X - 1) * (X + 1)⁻¹ = (2:ℂ) • (X + 1)⁻¹ := by sorry
