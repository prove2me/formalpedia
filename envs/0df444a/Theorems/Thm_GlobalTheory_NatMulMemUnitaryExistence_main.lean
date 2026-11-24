-- Prove2me | Theorems.Thm_GlobalTheory_NatMulMemUnitaryExistence_main
-- name    : GlobalTheory.NatMulMemUnitaryExistence.main
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:35:13.988565+00:00
-- url     : https://prove2.me/theorems/5717a1a4-a54a-4659-95ed-ae077893e1af
-- title:
--   Nat Mul Mem Unitary Existence: main
-- statement:
--   The Nat Mul Mem Unitary Existence construction uses the main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsNatMulMem.lean#L19-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsNatMulMem.lean#L19-L46

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsNatMulMem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.NatMulMemUnitaryExistence
open NumberField

theorem GlobalTheory.NatMulMemUnitaryExistence.main {E : Type} [Field E] [NumberField E] {n : ℕ}
    (L : Submodule (𝓞 E) (Fin n → E))
    (hL : Submodule.span E (L : Set (Fin n → E)) = ⊤) (x : Fin n → E) :
    ∃ d : ℕ, 0 < d ∧ d • x ∈ L := by sorry
