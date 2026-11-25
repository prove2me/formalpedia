-- Prove2me | Theorems.Thm_GlobalTheory_RealWeil_metaplectic_schwartz_smooth
-- name    : GlobalTheory.RealWeil.metaplectic_schwartz_smooth
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T00:16:23.073008+00:00
-- url     : https://prove2.me/theorems/ae347005-ea73-4f21-9763-5f104e78833a
-- title:
--   Real Weil: metaplectic schwartz smooth
-- statement:
--   The Real Weil construction uses the metaplectic schwartz smooth property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IteratedLineDerivMemWeylAlg.lean#L420-L444
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IteratedLineDerivMemWeylAlg.lean#L420-L444

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

theorem GlobalTheory.RealWeil.metaplectic_schwartz_smooth [TopologicalSpace G]
    (h3 : ∀ (g : G) (w : l ⊕ l → ℝ) (f : L2 l),
      om g (rho w f) = rho ((pr g : Matrix (l ⊕ l) (l ⊕ l) ℝ) *ᵥ w) (om g f))
    (h4 : ∀ (g : G) (f : Sch l), om g (f.toLp 2 volume) = (omS g f).toLp 2 volume)
    (h5 : ∀ (k : ℕ) (γ : (Fin k → ℝ) → G), Continuous γ →
      (∀ a b, ContDiff ℝ ∞ fun t => (pr (γ t) : Matrix (l ⊕ l) (l ⊕ l) ℝ) a b) →
      ∀ f : Sch l, ContDiff ℝ ∞ fun t => om (γ t) (f.toLp 2 volume)) :
    (∀ (g : G) (w : l ⊕ l → ℝ) (f : Sch l),
      omS g (dRho w f) = dRho ((pr g : Matrix (l ⊕ l) (l ⊕ l) ℝ) *ᵥ w) (omS g f)) ∧
    (∀ (lam : Sch l →L[ℂ] ℂ) (k : ℕ) (γ : (Fin k → ℝ) → G), Continuous γ →
      (∀ a b, ContDiff ℝ ∞ fun t => (pr (γ t) : Matrix (l ⊕ l) (l ⊕ l) ℝ) a b) →
      ∀ f : Sch l, ContDiff ℝ ∞ fun t => lam (omS (γ t) f)) ∧
    (∀ (lam : Sch l →L[ℂ] ℂ), ∀ X ∈ LieAlgebra.Symplectic.sp l ℝ, ∀ γ : ℝ → G, γ 0 = 1 →
      (∀ t, (pr (γ t) : Matrix (l ⊕ l) (l ⊕ l) ℝ) = NormedSpace.exp (t • X)) →
      (∀ f : Sch l, HasDerivAt (fun t => om (γ t) (f.toLp 2 volume)) ((quad X f).toLp 2 volume) 0) →
      ∀ f : Sch l, HasDerivAt (fun t => lam (omS (γ t) f)) (lam (quad X f)) 0) := by sorry
