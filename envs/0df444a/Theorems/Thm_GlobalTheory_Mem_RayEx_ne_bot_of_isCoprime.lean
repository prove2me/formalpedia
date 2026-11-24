-- Prove2me | Theorems.Thm_GlobalTheory_Mem_RayEx_ne_bot_of_isCoprime
-- name    : GlobalTheory.Mem.RayEx.ne_bot_of_isCoprime
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T22:45:57.063596+00:00
-- url     : https://prove2.me/theorems/2e8d7217-a631-4752-81c7-24316d39ee69
-- title:
--   Ray Ex: ne bot of is Coprime
-- statement:
--   The Ray Ex construction uses the ne bot of is Coprime property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/RayDataNonempty.lean#L35-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/RayDataNonempty.lean#L35-L38

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

theorem GlobalTheory.Mem.RayEx.ne_bot_of_isCoprime (hm : m ≠ ⊤) {I : Ideal R} (h : IsCoprime I m) : I ≠ ⊥ := by sorry
