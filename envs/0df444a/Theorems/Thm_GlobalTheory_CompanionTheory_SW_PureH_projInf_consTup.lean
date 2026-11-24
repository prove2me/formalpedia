-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_PureH_projInf_consTup
-- name    : GlobalTheory.CompanionTheory.SW.PureH.projInf_consTup
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T12:09:00.346449+00:00
-- url     : https://prove2.me/theorems/90cc8883-e91c-4a1f-9504-e62395828e50
-- title:
--   Pure H: proj Inf cons Tup
-- statement:
--   The Pure H construction uses the proj Inf cons Tup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/AdelicUnitaryFiniteSetDecomposition.lean#L37-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/AdelicUnitaryFiniteSetDecomposition.lean#L37-L39

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_BlockOneDetHermitianGram
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_AdelicUnitaryGroupProjections
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_LatticeStableAlmostEverywhere
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_AdelicUnitaryFiniteSetDecomposition
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PureH
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

theorem GlobalTheory.CompanionTheory.SW.PureH.projInf_consTup {M n : ℕ} (X : Fin n → Fin M → AF F ⊗[F] E) :
    projInf (consTup X) = consTup (projInf X) := by sorry
