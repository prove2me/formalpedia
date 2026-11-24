-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_QLTop_isOpen_intSet
-- name    : GlobalTheory.CompanionTheory.QLTop.isOpen_intSet
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T11:55:57.042352+00:00
-- url     : https://prove2.me/theorems/1c492c03-9398-4791-8593-2b897c60bccf
-- title:
--   QLTop: is Open int Set
-- statement:
--   The QLTop construction uses the is Open int Set property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/GeneralLinearIntegralCompactOpen.lean#L33-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/GeneralLinearIntegralCompactOpen.lean#L33-L38

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
omit [ValuativeRel F] [IsNonarchimedeanLocalField F]

theorem GlobalTheory.CompanionTheory.QLTop.isOpen_intSet {O : Subring F} (hO : IsOpen (O : Set F)) (n : ℕ) : IsOpen (intSet O n) := by sorry
