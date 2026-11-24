-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_PureH_consTup_empty
-- name    : GlobalTheory.CompanionTheory.SW.PureH.consTup_empty
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T12:07:44.052803+00:00
-- url     : https://prove2.me/theorems/10a1b39e-cd61-4efc-b41e-7b3d07bd4240
-- title:
--   Pure H: cons Tup empty
-- statement:
--   The Pure H construction uses the cons Tup empty property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/AdelicUnitaryFiniteSetDecomposition.lean#L26-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/AdelicUnitaryFiniteSetDecomposition.lean#L26-L31

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

theorem GlobalTheory.CompanionTheory.SW.PureH.consTup_empty {K : Type} [Zero K] [One K] {M : ℕ} (X : Fin 0 → Fin M → K) :
    (consTup X : Fin (0 + 1) → Fin (M + 1) → K) = fun _ : Fin 1 => Fin.cons 1 (fun _ => 0) := by sorry
