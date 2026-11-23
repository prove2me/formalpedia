-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_StabFirst_of_blockGL_mem_UJ
-- name    : GlobalTheory.CompanionTheory.SW.StabFirst.of_blockGL_mem_UJ
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:31:07.207901+00:00
-- url     : https://prove2.me/theorems/23b07d38-fd1e-449e-8448-b2d8fd0f91f5
-- title:
--   Stab First: of block GL mem UJ
-- statement:
--   The Stab First construction uses the of block GL mem UJ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/BlockOneRightInjective.lean#L75-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/BlockOneRightInjective.lean#L75-L80

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_BlockOneRightInjective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.StabFirst
variable {K : Type} [CommRing K] {M : ℕ}

theorem GlobalTheory.CompanionTheory.SW.StabFirst.of_blockGL_mem_UJ (σ : K →+* K) (J : Matrix (Fin M) (Fin M) K) (s : K) {g : GL (Fin M) K}
    (hg : blockGL g ∈ UJ σ (blockOne s J)) : g ∈ UJ σ J := by sorry
