-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_HProj_act_inv
-- name    : GlobalTheory.CompanionTheory.SW.HProj.act_inv
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T12:04:50.697858+00:00
-- url     : https://prove2.me/theorems/98ed1c14-4a9f-414a-b0e6-7e0dea41eefa
-- title:
--   HProj: act inv
-- statement:
--   The HProj construction uses the act inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/AdelicUnitaryGroupProjections.lean#L169-L174
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/AdelicUnitaryGroupProjections.lean#L169-L174

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_AdelicTupleProjectionsStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_AdelicUnitaryGroupProjections
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
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.HProj
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {d : ℕ}

theorem GlobalTheory.CompanionTheory.SW.HProj.act_inv (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) {M n : ℕ}
    (J : Matrix (Fin M) (Fin M) E) (g : HA R σ J) (X : Fin n → Fin M → R ⊗[F] E) :
    actW R σ J g⁻¹ (actW R σ J g X) = X := by sorry
