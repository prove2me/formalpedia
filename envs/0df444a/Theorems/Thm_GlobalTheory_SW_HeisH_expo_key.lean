-- Prove2me | Theorems.Thm_GlobalTheory_SW_HeisH_expo_key
-- name    : GlobalTheory.SW.HeisH.expo_key
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T19:40:49.430894+00:00
-- url     : https://prove2.me/theorems/737a4ffe-5434-4ec1-91c2-840325f428c4
-- title:
--   Heis H: expo key
-- statement:
--   The Heis H construction uses the expo key property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/HermitianHeisenbergOperatorLaws.lean#L17-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SiegelThetaTransformation/HermitianHeisenbergOperatorLaws.lean#L17-L42

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ThHEqThSDictionary
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_UnitaryActHalfSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianWeilActionUnitaryGroupTestFunctionsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_HermitianHeisenbergOperatorLaws
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.HeisH
noncomputable section
variable {n N : ℕ}

theorem GlobalTheory.SW.HeisH.expo_key {Ji Jp W Z K : Matrix (Fin N) (Fin N) ℂ}
    {P Q P' Q' w : Matrix (Fin n) (Fin N) ℂ} {Ps Qs Ps' Qs' u : Matrix (Fin N) (Fin n) ℂ}
    (hr : (Q + P * Z) * Ji = Q' + P' * W) (hs : Jp * (Qs + Z * Ps) = Qs' + W * Ps')
    (hrK : (Q + P * Z) * K = P - P' * Jp)
    (hKs : K * (Qs + Z * Ps) = Ps - Ji * Ps') :
    2 * ((P' * W * Ps').trace + (P' * (Jp * u)).trace + (w * Ji * Ps').trace) +
      ((Q' * Ps').trace + (P' * Qs').trace) +
      2 * ((w + Q + P * Z) * K * (u + Qs + Z * Ps)).trace =
    2 * (w * K * u).trace + (2 * ((P * Z * Ps).trace + (P * u).trace + (w * Ps).trace) +
      ((Q * Ps).trace + (P * Qs).trace)) := by sorry
