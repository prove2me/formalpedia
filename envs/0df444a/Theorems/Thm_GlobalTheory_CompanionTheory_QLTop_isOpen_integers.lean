-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_QLTop_isOpen_integers
-- name    : GlobalTheory.CompanionTheory.QLTop.isOpen_integers
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T11:55:46.994791+00:00
-- url     : https://prove2.me/theorems/90fb875e-9257-48ca-bf28-7c3adcf6ac90
-- title:
--   QLTop: is Open integers
-- statement:
--   The QLTop construction uses the is Open integers property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/LocalFieldTopologyNormBalls.lean#L10-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/LocalFieldTopologyNormBalls.lean#L10-L14

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_InstBorelGL
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_T2SpaceOfIsNonarchimedeanLocalFieldFlagMeasures
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_LocalFieldTopologyNormBalls
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix GlobalTheory.CompanionTheory.QL
open scoped ComplexConjugate ValuativeRel
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.QLTop

theorem GlobalTheory.CompanionTheory.QLTop.isOpen_integers (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] :
    IsOpen ((𝒪[F] : Subring F) : Set F) := by sorry
