-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_QLTop_isOpen_isCompact_integers
-- name    : GlobalTheory.CompanionTheory.QLTop.isOpen_isCompact_integers
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T11:55:45.23098+00:00
-- url     : https://prove2.me/theorems/43d987d8-e789-48b0-a27e-2671f2447036
-- title:
--   QLTop: is Open is Compact integers
-- statement:
--   The QLTop construction uses the is Open is Compact integers property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/GeneralLinearIntegralCompactOpen.lean#L25-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/GeneralLinearIntegralCompactOpen.lean#L25-L28

import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_InstBorelGL
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_GeneralLinearIntegralCompactOpen
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
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.QLTop
open ValuativeRel
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

theorem GlobalTheory.CompanionTheory.QLTop.isOpen_isCompact_integers : IsOpen ((𝒪[F] : Subring F) : Set F) ∧ IsCompact ((𝒪[F] : Subring F) : Set F) := by sorry
