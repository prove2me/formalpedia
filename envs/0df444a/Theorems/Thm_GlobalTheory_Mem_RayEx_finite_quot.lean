-- Prove2me | Theorems.Thm_GlobalTheory_Mem_RayEx_finite_quot
-- name    : GlobalTheory.Mem.RayEx.finite_quot
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T22:45:36.699282+00:00
-- url     : https://prove2.me/theorems/c81763d3-c51c-4d3b-9288-49a9c9851816
-- title:
--   Ray Ex: finite quot
-- statement:
--   The Ray Ex construction uses the finite quot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/RayDataNonempty.lean#L120-L139
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/RayDataNonempty.lean#L120-L139

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

theorem GlobalTheory.Mem.RayEx.finite_quot (hm : m ≠ ⊤) [Finite (R ⧸ m)] [Finite (ClassGroup R)] : Finite (con m).Quotient := by sorry
