-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_ThW_toA_dotProduct_Bf
-- name    : GlobalTheory.CompanionTheory.SW.ThW.toA_dotProduct_Bf
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T12:11:01.084672+00:00
-- url     : https://prove2.me/theorems/1d0dbb2b-b97b-478d-a0a7-4570f9b04323
-- title:
--   Th W: to A dot Product Bf
-- statement:
--   The Th W construction uses the to A dot Product Bf property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/AdelicCharacterExponentialFormula.lean#L36-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/AdelicCharacterExponentialFormula.lean#L36-L39

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_SumRhoEqTrace
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_AdelicCharacterExponentialFormula
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.ThW
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups Kronecker

theorem GlobalTheory.CompanionTheory.SW.ThW.toA_dotProduct_Bf {F : Type} [Field F] [NumberField F] {ι : Type} [Fintype ι]
    (B : Matrix ι ι F) (a y : ι → F) :
    toA a ⬝ᵥ (Bf B *ᵥ toA y) = algebraMap F (A F) (a ⬝ᵥ (B *ᵥ y)) := by sorry
