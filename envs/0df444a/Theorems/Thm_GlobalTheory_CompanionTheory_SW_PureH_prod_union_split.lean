-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_PureH_prod_union_split
-- name    : GlobalTheory.CompanionTheory.SW.PureH.prod_union_split
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:30:01.444147+00:00
-- url     : https://prove2.me/theorems/7270e16d-370e-457c-ae73-1644a229d3c7
-- title:
--   Pure H: prod union split
-- statement:
--   The Pure H construction uses the prod union split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/AdelicUnitaryFiniteSetDecomposition.lean#L74-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/AdelicUnitaryFiniteSetDecomposition.lean#L74-L80

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
  [DecidableEq (HeightOneSpectrum (𝓞 F))]

theorem GlobalTheory.CompanionTheory.SW.PureH.prod_union_split {ι : Type} [DecidableEq ι] (S Sh : Finset ι) (A B : ι → ℝ≥0∞) (P : ι → Prop)
    [DecidablePred P] (hS : ∀ v, P v ↔ v ∈ S) :
    ∏ v ∈ S ∪ Sh, (if P v then A v else B v) = (∏ v ∈ S, A v) * ∏ v ∈ Sh \ S, B v := by sorry
