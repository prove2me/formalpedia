-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SdFin_exists_of_std
-- name    : GlobalTheory.CompanionTheory.SdFin.exists_of_std
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T13:59:51.620797+00:00
-- url     : https://prove2.me/theorems/8dcf583f-09da-4db0-8e16-6787ef571a79
-- title:
--   Sd Fin: exists of std
-- statement:
--   The Sd Fin construction uses the exists of std property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/HermitianForms/ExistsSdWSdHerm.lean#L21-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/HermitianForms/ExistsSdWSdHerm.lean#L21-L81

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
open GlobalTheory.JR.DualLattice
variable {K : Type} [NontriviallyNormedField K] [IsUltrametricDist K] [LocallyCompactSpace K]

theorem GlobalTheory.CompanionTheory.SdFin.exists_of_std (ψ : AddChar K ℂ) (hψ : GlobalTheory.JR.IsStdChar ψ) (hu : ∀ t, ‖ψ t‖ = 1)
    (V : Type) [AddCommGroup V] [Module K V] [Module.Finite K V] [TopologicalSpace V]
    [IsModuleTopology K V] [IsTopologicalAddGroup V] [LocallyCompactSpace V]
    [SecondCountableTopology V] [T2Space V] [MeasurableSpace V] [BorelSpace V]
    (β : LinearMap.BilinForm K V) (hs : β.IsSymm) (hβ : β.Nondegenerate) :
    ∃ μ : Measure V, SelfDual μ (fun x y => ψ (β x y)) := by sorry
