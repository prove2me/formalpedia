-- Prove2me | Theorems.Thm_GlobalTheory_Mem_RayEx_isCoprime_span
-- name    : GlobalTheory.Mem.RayEx.isCoprime_span
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T22:45:42.964617+00:00
-- url     : https://prove2.me/theorems/3c07229c-d401-41a4-a4f8-2778dd2817c0
-- title:
--   Ray Ex: is Coprime span
-- statement:
--   The Ray Ex construction uses the is Coprime span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/RayDataNonempty.lean#L47-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/RayDataNonempty.lean#L47-L48

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

theorem GlobalTheory.Mem.RayEx.isCoprime_span {a : R} (ha : a - 1 ∈ m) : IsCoprime (Ideal.span {a}) m := by sorry
