-- Prove2me | Theorems.Thm_GlobalTheory_RealWeil_contDiff_toLp_omS
-- name    : GlobalTheory.RealWeil.contDiff_toLp_omS
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T19:16:29.40652+00:00
-- url     : https://prove2.me/theorems/f5731003-9c9c-4ef1-983b-ae6033526f3e
-- title:
--   Real Weil: cont Diff to Lp om S
-- statement:
--   The Real Weil construction uses the cont Diff to Lp om S property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IteratedLineDerivMemWeylAlg.lean#L334-L360
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IteratedLineDerivMemWeylAlg.lean#L334-L360

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_RealMetaplecticRepresentation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IteratedLineDerivMemWeylAlg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex SchwartzMap LineDeriv Matrix
open scoped Real RealInnerProductSpace ContDiff FourierTransform
open GlobalTheory GlobalTheory.RealWeil
variable {l : Type} [Fintype l]
variable [DecidableEq l]
variable {G : Type} [Group G] {pr : G →* Matrix.symplecticGroup l ℝ} {om : G →* (L2 l ≃ₗᵢ[ℂ] L2 l)}
  {omS : G →* (Sch l →L[ℂ] Sch l)}

theorem GlobalTheory.RealWeil.contDiff_toLp_omS
    (h3 : ∀ (g : G) (w : l ⊕ l → ℝ) (f : L2 l),
      om g (rho w f) = rho ((pr g : Matrix (l ⊕ l) (l ⊕ l) ℝ) *ᵥ w) (om g f))
    (h4 : ∀ (g : G) (f : Sch l), om g (f.toLp 2 volume) = (omS g f).toLp 2 volume)
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {γ : E → G}
    (hγ : ∀ a b, ContDiff ℝ ∞ fun t => (pr (γ t) : Matrix (l ⊕ l) (l ⊕ l) ℝ) a b)
    (h5 : ∀ f : Sch l, ContDiff ℝ ∞ fun t => om (γ t) (f.toLp 2 volume)) {A : Sch l →L[ℂ] Sch l} (hA : A ∈ weylAlg l)
    (f : Sch l) : ContDiff ℝ ∞ fun t => schwartzToL2 l (A (omS (γ t) f)) := by sorry
