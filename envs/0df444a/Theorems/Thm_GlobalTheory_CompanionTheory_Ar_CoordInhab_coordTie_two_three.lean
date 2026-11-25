-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ar_CoordInhab_coordTie_two_three
-- name    : GlobalTheory.CompanionTheory.Ar.CoordInhab.coordTie_two_three
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T11:58:31.956747+00:00
-- url     : https://prove2.me/theorems/e474bb50-308f-5097-bc8d-8f4013558b3b
-- title:
--   Coord Inhab: coord Tie two three
-- statement:
--   The Coord Inhab construction uses the coord Tie two three property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GeometryProofs/StalkClosedPointToToStalk.lean#L182-L185
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GeometryProofs/StalkClosedPointToToStalk.lean#L182-L185

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_CoordsAt
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_InjectiveOfIsCptGen
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GeometryProofs_StalkClosedPointToToStalk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar
open AlgebraicGeometry CategoryTheory CptModel
open CoordInhab
open GlobalTheory.CompanionTheory.Ar.CoordInhab

theorem GlobalTheory.CompanionTheory.Ar.CoordInhab.coordTie_two_three :
    CoordTie ℤ (Spec.map (CommRingCat.ofHom (algebraMap ℤ ℚ)))
      (fun j => algebraMap ℤ ℚ ((![2, 3] : Fin 2 → ℤ) j)) := by sorry
