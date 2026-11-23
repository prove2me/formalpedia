-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_MeasProj_projV_mem_latV_iff
-- name    : GlobalTheory.CompanionTheory.SW.MeasProj.projV_mem_latV_iff
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T07:29:44.372811+00:00
-- url     : https://prove2.me/theorems/dd196fba-7c81-4812-82db-d5569323eaba
-- title:
--   Meas Proj: proj V mem lat V iff
-- statement:
--   The Meas Proj construction uses the proj V mem lat V iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/AdelicTupleProjections.lean#L102-L107
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/AdelicTupleProjections.lean#L102-L107

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorLocallyCompactRing
import Definitions.Def_GroundTheory_GlobalFields_LocalAtPlace
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_AdelicTupleProjections
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.MeasProj
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

theorem GlobalTheory.CompanionTheory.SW.MeasProj.projV_mem_latV_iff {d n M : ℕ} (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F))
    (X : Fin n → Fin M → Af F ⊗[F] E) :
    projV v X ∈ (latV b v : Set (Fin n → Fin M → Fv F v ⊗[F] E)) ↔
      ∀ a i k, ((Algebra.TensorProduct.basis (Af F) b).repr (X a i) k) v ∈
        v.adicCompletionIntegers F := by sorry
