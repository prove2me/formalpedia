-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_Glue_crd_v
-- name    : GlobalTheory.CompanionTheory.SW.Glue.crd_v
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:50:48.330771+00:00
-- url     : https://prove2.me/theorems/445828db-ea94-4c32-8dbf-91c767c40683
-- title:
--   Glue: crd v
-- statement:
--   The Glue construction uses the crd v property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/AdelicTupleLocalGlobalProperties.lean#L73-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/AdelicTupleLocalGlobalProperties.lean#L73-L80

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_HypJ
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_AdelicTupleLocalGlobalProperties
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix RestrictedProduct
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.Glue
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
variable {d M n : ℕ} (b : Module.Basis (Fin d) F E)

theorem GlobalTheory.CompanionTheory.SW.Glue.crd_v (v : HeightOneSpectrum (𝓞 F)) (X : Fin n → Fin M → AF F ⊗[F] E)
    (a : Fin n) (i : Fin M) (k : Fin d) :
    (Algebra.TensorProduct.basis (Fv F v) b).repr (projV v (projFin X) a i) k =
      pV v ((Algebra.TensorProduct.basis (AF F) b).repr (X a i) k) := by sorry
