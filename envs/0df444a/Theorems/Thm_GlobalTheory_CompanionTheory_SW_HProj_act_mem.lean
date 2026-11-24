-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_HProj_act_mem
-- name    : GlobalTheory.CompanionTheory.SW.HProj.act_mem
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T12:04:45.386292+00:00
-- url     : https://prove2.me/theorems/6a54456a-7ca5-49b9-bc57-35f45f67bafd
-- title:
--   HProj: act mem
-- statement:
--   The HProj construction uses the act mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/AdelicUnitaryGroupProjections.lean#L157-L167
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/AdelicUnitaryGroupProjections.lean#L157-L167

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

theorem GlobalTheory.CompanionTheory.SW.HProj.act_mem {M n : ℕ} (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F))
    (hm : ∀ y z : Fv F v ⊗[F] E, y ∈ Lv b v → z ∈ Lv b v → y * z ∈ Lv b v)
    (G : Matrix (Fin M) (Fin M) (Fv F v ⊗[F] E)) (hG : ∀ i j, G i j ∈ Lv b v)
    (X : Fin n → Fin M → Fv F v ⊗[F] E) (hX : X ∈ latV b v) :
    (fun a => G.mulVec (X a)) ∈ latV b v := by sorry
