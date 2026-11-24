-- Prove2me | Theorems.Thm_GlobalTheory_RealWeil_hasDerivAt_toLp_omS
-- name    : GlobalTheory.RealWeil.hasDerivAt_toLp_omS
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T19:16:08.503538+00:00
-- url     : https://prove2.me/theorems/977e8cd9-62e0-4f71-b601-0d2d839b653d
-- title:
--   Real Weil: has Deriv At to Lp om S
-- statement:
--   The Real Weil construction uses the has Deriv At to Lp om S property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IteratedLineDerivMemWeylAlg.lean#L370-L418
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IteratedLineDerivMemWeylAlg.lean#L370-L418

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

theorem GlobalTheory.RealWeil.hasDerivAt_toLp_omS
    (h3 : ∀ (g : G) (w : l ⊕ l → ℝ) (f : L2 l),
      om g (rho w f) = rho ((pr g : Matrix (l ⊕ l) (l ⊕ l) ℝ) *ᵥ w) (om g f))
    (h4 : ∀ (g : G) (f : Sch l), om g (f.toLp 2 volume) = (omS g f).toLp 2 volume)
    {X : Matrix (l ⊕ l) (l ⊕ l) ℝ} (hX : X ∈ LieAlgebra.Symplectic.sp l ℝ) {γ : ℝ → G} (h0 : γ 0 = 1)
    (hγ : ∀ t, (pr (γ t) : Matrix (l ⊕ l) (l ⊕ l) ℝ) = NormedSpace.exp (t • X))
    (h6 : ∀ f : Sch l, HasDerivAt (fun t => om (γ t) (f.toLp 2 volume)) ((quad X f).toLp 2 volume) 0)
    {A : Sch l →L[ℂ] Sch l} (hA : A ∈ weylAlg l) (f : Sch l) :
    HasDerivAt (fun t => schwartzToL2 l (A (omS (γ t) f))) (schwartzToL2 l (A (quad X f))) 0 := by sorry
