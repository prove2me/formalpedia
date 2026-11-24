-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SdFin_exists_of_bilin
-- name    : GlobalTheory.CompanionTheory.SdFin.exists_of_bilin
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T14:00:33.470592+00:00
-- url     : https://prove2.me/theorems/bcff523d-d1ea-47dc-93d2-c19693c5b76f
-- title:
--   Sd Fin: exists of bilin
-- statement:
--   The Sd Fin construction uses the exists of bilin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/HermitianForms/ExistsSdWSdHerm.lean#L95-L148
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/HermitianForms/ExistsSdWSdHerm.lean#L95-L148

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_SiegelWeilUnitaryConvergent
import Definitions.Def_Formalism_UnipotentAdelicQuotients_StdAdditiveCharExists
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_HermitianForms_IndicatorInSchrodingerSpanStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_HermitianForms_AdelicCharacterLocalNontrivial
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsSmallDualLattices
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_AdditiveCharConductorExists
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Tjcosets
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_HermitianForms_ExistsSdWSdHerm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain MeasureTheory HeckeCharacterZeroLocus.SiegelWeilU Topology
open scoped TensorProduct
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SdFin
variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

theorem GlobalTheory.CompanionTheory.SdFin.exists_of_bilin (ψ : AddChar (Fv F v) ℂ) (hψ : Continuous ψ) (hu : ∀ t, ‖ψ t‖ = 1)
    (hne : ∃ t, ψ t ≠ 1) (V : Type) [AddCommGroup V] [Module (Fv F v) V] [Module.Finite (Fv F v) V]
    [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousSMul (Fv F v) V] [T2Space V]
    [MeasurableSpace V] [BorelSpace V]
    (β : LinearMap.BilinForm (Fv F v) V) (hs : ∀ x y, β x y = β y x)
    (hn : ∀ x, (∀ y, β x y = 0) → x = 0) :
    ∃ μ : Measure V, SelfDual μ (fun x y => ψ (β x y)) := by sorry
