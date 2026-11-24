-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_PureH_pureL_act_vec
-- name    : GlobalTheory.CompanionTheory.SW.PureH.pureL_act_vec
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T12:08:19.600954+00:00
-- url     : https://prove2.me/theorems/1d6786a6-ee1c-4959-8544-d654dc0913b3
-- title:
--   Pure H: pure L act vec
-- statement:
--   The Pure H construction uses the pure L act vec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/AdelicUnitaryFiniteSetDecomposition.lean#L153-L178
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/AdelicUnitaryFiniteSetDecomposition.lean#L153-L178

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
variable {d M : ℕ} (b : Module.Basis (Fin d) F E) (σ : E →ₐ[F] E)
  (Jp : Matrix (Fin (M + 1)) (Fin (M + 1)) E) (h : HA (AF F) σ Jp) (ginf : HA (Ainf F) σ Jp)
  (g : ∀ v : HeightOneSpectrum (𝓞 F), HA (Fv F v) σ Jp) (S Sh : Finset (HeightOneSpectrum (𝓞 F)))
include b

theorem GlobalTheory.CompanionTheory.SW.PureH.pureL_act_vec
    (hinf : ∀ (n : ℕ) (X : Fin n → Fin (M + 1) → AF F ⊗[F] E),
      projInf (actW (AF F) σ Jp h X) = actW (Ainf F) σ Jp ginf (projInf X))
    (hfin : ∀ (n : ℕ) (X : Fin n → Fin (M + 1) → AF F ⊗[F] E) (v : HeightOneSpectrum (𝓞 F)),
      projV v (projFin (actW (AF F) σ Jp h X)) = actW (Fv F v) σ Jp (g v) (projV v (projFin X)))
    (hSh : ∀ v, v ∉ Sh → ∀ (n : ℕ) (X : Fin n → Fin (M + 1) → Fv F v ⊗[F] E),
      actW (Fv F v) σ Jp (g v) X ∈ latV b v ↔ X ∈ latV b v)
    (hS : ∀ v, v ∉ S → ∀ X₀ : Fin 0 → Fin M → Fv F v ⊗[F] E, consTup X₀ ∈ latV b v)
    (Ψinf : (Fin 1 → Fin (M + 1) → Ainf F ⊗[F] E) → ℝ≥0∞)
    (Ψ : ∀ v : HeightOneSpectrum (𝓞 F), (Fin 1 → Fin (M + 1) → Fv F v ⊗[F] E) → ℝ≥0∞) :
    pureL b S Ψinf Ψ (actW (AF F) σ Jp h (fun _ : Fin 1 => Fin.cons 1 (fun _ => 0))) =
      (Ψinf (actW (Ainf F) σ Jp ginf (fun _ : Fin 1 => Fin.cons 1 (fun _ => 0))) *
        ∏ v ∈ S, Ψ v (actW (Fv F v) σ Jp (g v) (fun _ : Fin 1 => Fin.cons 1 (fun _ => 0)))) *
        ∏ v ∈ Sh \ S, (latV b v).indicator 1
          (actW (Fv F v) σ Jp (g v) (fun _ : Fin 1 => Fin.cons 1 (fun _ => 0))) := by sorry
