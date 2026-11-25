-- Prove2me | Theorems.Thm_GlobalTheory_CechMixed_le_iSup_inf
-- name    : GlobalTheory.CechMixed.le_iSup_inf
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T16:09:53.442096+00:00
-- url     : https://prove2.me/theorems/e0d3ceaf-9085-4774-a327-f88eeee308ea
-- title:
--   Cech Mixed: le i Sup inf
-- statement:
--   The Cech Mixed construction uses the le i Sup inf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsCechOneCocycleOnAffineCoverMixed.lean#L21-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsCechOneCocycleOnAffineCoverMixed.lean#L21-L23

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_IsInvDer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_LeISupInfPreimage
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsCobOfIsAffineOpen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsCechOneCocycleOnAffineCoverMixed
import Theorems.Thm_GlobalTheory_AbLaw_CechOne_le_iSup_inf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits
open GlobalTheory.KS (rsT C1 IsCoc IsCob)
open GlobalTheory GlobalTheory.CechMixed
open GlobalTheory.KS

theorem GlobalTheory.CechMixed.le_iSup_inf {X : Scheme.{0}} {J : Type} {V : J → X.Opens} (hV : ⨆ i, V i = ⊤) (O : X.Opens) :
    O ≤ ⨆ i, V i ⊓ O := by sorry
