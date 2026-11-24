-- Prove2me | Theorems.Thm_GlobalTheory_GaussTransport_hasTemperateGrowth_chirp
-- name    : GlobalTheory.GaussTransport.hasTemperateGrowth_chirp
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T13:54:08.567478+00:00
-- url     : https://prove2.me/theorems/0b498048-8389-4ccc-9dff-244a38278c99
-- title:
--   Gauss Transport: has Temperate Growth chirp
-- statement:
--   The Gauss Transport construction uses the has Temperate Growth chirp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SchwartzDensityTransportLinearEquivChirp.lean#L28-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SchwartzDensityTransportLinearEquivChirp.lean#L28-L36

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzDensityTransportLinearEquivChirp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open FourierTransform MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.GaussTransport

theorem GlobalTheory.GaussTransport.hasTemperateGrowth_chirp {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (Q : V →L[ℝ] V →L[ℝ] ℂ) (s : ℝ) :
    Function.HasTemperateGrowth (fun x : V => Complex.exp (Complex.I * ((s * (Q x x).im : ℝ) : ℂ))) := by sorry
