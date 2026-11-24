-- Prove2me | Theorems.Thm_GlobalTheory_Mem_RayEx_ne_zero_of_sub_one_mem
-- name    : GlobalTheory.Mem.RayEx.ne_zero_of_sub_one_mem
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T22:45:20.390272+00:00
-- url     : https://prove2.me/theorems/89cdac7e-fbf2-4cc6-aaa1-5008229b4798
-- title:
--   Ray Ex: ne zero of sub one mem
-- statement:
--   The Ray Ex construction uses the ne zero of sub one mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/RayDataNonempty.lean#L29-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/RayDataNonempty.lean#L29-L33

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_NonemptyRayDataOfNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_RayDataNonempty
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.Mem GlobalTheory.Mem.RayEx
open NumberField IsDedekindDomain
variable {R : Type} [CommRing R] [IsDedekindDomain R] (m : Ideal R)
variable {m}

theorem GlobalTheory.Mem.RayEx.ne_zero_of_sub_one_mem (hm : m ≠ ⊤) {a : R} (ha : a - 1 ∈ m) : a ≠ 0 := by sorry
