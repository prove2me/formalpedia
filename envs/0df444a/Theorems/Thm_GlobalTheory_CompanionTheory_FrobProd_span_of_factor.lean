-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_FrobProd_span_of_factor
-- name    : GlobalTheory.CompanionTheory.FrobProd.span_of_factor
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T11:42:31.348773+00:00
-- url     : https://prove2.me/theorems/d0059fa6-ba4b-4f6b-9780-6c0cb42c6e95
-- title:
--   Frob Prod: span of factor
-- statement:
--   The Frob Prod construction uses the span of factor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/SchwartzBruhatProdSpanTensors.lean#L61-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/SchwartzBruhatProdSpanTensors.lean#L61-L120

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_AutomorphicKernels_BernsteinUnitaryProducts_BernsteinTheoremA_FrobeniusReciprocity_SupportedInIffOfFrob
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SchwartzBruhatProdSpanTensors
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory MeasureTheory.Measure GlobalTheory.SplitWeil PositivityTheory.PfBern.Frob
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.FrobProd
open Classical

theorem GlobalTheory.CompanionTheory.FrobProd.span_of_factor {A B S T : Type} [TopologicalSpace A] [T2Space A] [TopologicalSpace B]
    [T2Space B] [Fintype S] [Fintype T] {ξ : A → S} {η : B → T}
    (hξ : IsLocallyConstant ξ) (hη : IsLocallyConstant η) (s0 : S) (t0 : T)
    (hcs : ∀ s, s ≠ s0 → IsCompact (ξ ⁻¹' {s})) (hct : ∀ t, t ≠ t0 → IsCompact (η ⁻¹' {t}))
    (f : SB (A × B))
    (hΦ : ∀ q q' : A × B, ξ q.1 = ξ q'.1 → η q.2 = η q'.2 →
      (f : A × B → ℂ) q = (f : A × B → ℂ) q')
    (h0 : ∀ q : A × B, ξ q.1 = s0 → (f : A × B → ℂ) q = 0)
    (h0' : ∀ q : A × B, η q.2 = t0 → (f : A × B → ℂ) q = 0) :
    (f : A × B → ℂ) ∈ Submodule.span ℂ {F : A × B → ℂ | ∃ a : SB A, ∃ b : SB B,
      (∀ q : A × B, (a : A → ℂ) q.1 ≠ 0 → (b : B → ℂ) q.2 ≠ 0 → (f : A × B → ℂ) q ≠ 0) ∧
        F = fun q => (a : A → ℂ) q.1 * (b : B → ℂ) q.2} := by sorry
