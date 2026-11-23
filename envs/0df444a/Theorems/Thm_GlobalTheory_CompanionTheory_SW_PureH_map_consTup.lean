-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_PureH_map_consTup
-- name    : GlobalTheory.CompanionTheory.SW.PureH.map_consTup
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:02:29.154736+00:00
-- url     : https://prove2.me/theorems/7c2604ae-1121-479a-bf22-5d74af5e3cec
-- title:
--   Pure H: map cons Tup
-- statement:
--   The Pure H construction uses the map cons Tup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/AdelicUnitaryFiniteSetDecomposition.lean#L12-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/AdelicUnitaryFiniteSetDecomposition.lean#L12-L24

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

theorem GlobalTheory.CompanionTheory.SW.PureH.map_consTup {K L : Type} [Zero K] [One K] [Zero L] [One L] (f : K → L) (h0 : f 0 = 0)
    (h1 : f 1 = 1) {M n : ℕ} (X : Fin n → Fin M → K) :
    (fun a i => f (consTup X a i)) = consTup (fun a i => f (X a i)) := by sorry
