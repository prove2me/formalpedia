-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SDPadic_trunc
-- name    : GlobalTheory.CompanionTheory.SDPadic.trunc
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T12:01:26.868385+00:00
-- url     : https://prove2.me/theorems/1051f0c8-430c-4eea-a974-190b99e66052
-- title:
--   SDPadic: trunc
-- statement:
--   The SDPadic construction uses the trunc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/HermitianForms/IndicatorInSchrodingerSpan.lean#L12-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/HermitianForms/IndicatorInSchrodingerSpan.lean#L12-L72

import Mathlib
import Definitions.Def_Formalism_UnipotentAdelicQuotients_SWXSDefs
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsSelfDualOfDualSubgroups
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_HermitianForms_IndicatorInSchrodingerSpan
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory HeckeCharacterZeroLocus.SiegelWeilU Filter Topology
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SDPadic
variable {V : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
  [MeasurableSpace V] [BorelSpace V] [T2Space V] [LocallyCompactSpace V] [SecondCountableTopology V]

theorem GlobalTheory.CompanionTheory.SDPadic.trunc (μ : Measure V) [μ.IsAddHaarMeasure] (B : V → V → ℂ)
    (hB : Continuous (fun p : V × V => B p.1 p.2)) (hs : ∀ x y, B x y = B y x)
    (ha : ∀ x x' y, B (x + x') y = B x y * B x' y) (M N : AddSubgroup V)
    (hMo : IsOpen (M : Set V)) (hNo : IsOpen (N : Set V)) (hNc : IsCompact (N : Set V))
    (hM : ∀ x, x ∈ M ↔ ∀ y ∈ N, B x y = 1)
    (f : V → ℂ) (hf : Continuous f) (hfc : HasCompactSupport f) (z : V) :
    ∫ y in (N : Set V), (∫ x, f x * B x y ∂μ) * B y z ∂μ
      = ∫ u in (M : Set V), (μ.real N : ℂ) * f (u - z) ∂μ := by sorry
