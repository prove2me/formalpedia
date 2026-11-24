-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_UnfoldAbs_integrable_of_lattice_bound
-- name    : GlobalTheory.CompanionTheory.UnfoldAbs.integrable_of_lattice_bound
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T12:19:43.514805+00:00
-- url     : https://prove2.me/theorems/73675b74-6087-4db7-8e88-bfd25dbd128f
-- title:
--   Unfold Abs: integrable of lattice bound
-- statement:
--   The Unfold Abs construction uses the integrable of lattice bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FundamentalDomainFourierUnfolding.lean#L48-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FundamentalDomainFourierUnfolding.lean#L48-L67

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FundamentalDomainFourierUnfolding
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open scoped Pointwise
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.UnfoldAbs

theorem GlobalTheory.CompanionTheory.UnfoldAbs.integrable_of_lattice_bound {A : Type} [AddCommGroup A] [MeasurableSpace A]
    [MeasurableAdd A] (lam : Measure A) [lam.IsAddLeftInvariant] (Λ : AddSubgroup A)
    [Countable Λ] (𝓖 : Set A) (h𝓖 : IsAddFundamentalDomain Λ 𝓖 lam) (h1 : lam 𝓖 = 1)
    (F0 : A → ℂ) (hm : AEStronglyMeasurable F0 lam) (M : ℝ)
    (hb : ∀ b, Summable (fun l : Λ => ‖F0 ((l : A) + b)‖) ∧ ∑' l : Λ, ‖F0 ((l : A) + b)‖ ≤ M) :
    Integrable F0 lam := by sorry
