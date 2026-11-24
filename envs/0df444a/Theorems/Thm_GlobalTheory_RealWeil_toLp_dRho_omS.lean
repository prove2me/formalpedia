-- Prove2me | Theorems.Thm_GlobalTheory_RealWeil_toLp_dRho_omS
-- name    : GlobalTheory.RealWeil.toLp_dRho_omS
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:55:52.955061+00:00
-- url     : https://prove2.me/theorems/f3c3ee76-7c6d-4646-a1bd-21e9c4c071af
-- title:
--   Real Weil: to Lp d Rho om S
-- statement:
--   The Real Weil construction uses the to Lp d Rho om S property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IteratedLineDerivMemWeylAlg.lean#L318-L332
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/IteratedLineDerivMemWeylAlg.lean#L318-L332

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

theorem GlobalTheory.RealWeil.toLp_dRho_omS
    (h3 : ∀ (g : G) (w : l ⊕ l → ℝ) (f : L2 l),
      om g (rho w f) = rho ((pr g : Matrix (l ⊕ l) (l ⊕ l) ℝ) *ᵥ w) (om g f))
    (h4 : ∀ (g : G) (f : Sch l), om g (f.toLp 2 volume) = (omS g f).toLp 2 volume) (A : Sch l →L[ℂ] Sch l) (g : G)
    (w : l ⊕ l → ℝ) (f : Sch l) :
    schwartzToL2 l ((A * dRho w) (omS g f)) = ∑ a,
      (((-(Matrix.J l ℝ * (pr g : Matrix (l ⊕ l) (l ⊕ l) ℝ)ᵀ * Matrix.J l ℝ)) *ᵥ w) a : ℂ) •
        schwartzToL2 l (A (omS g (dRho (Pi.single a 1) f))) := by sorry
