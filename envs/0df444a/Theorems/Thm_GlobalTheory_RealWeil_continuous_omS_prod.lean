-- Prove2me | Theorems.Thm_GlobalTheory_RealWeil_continuous_omS_prod
-- name    : GlobalTheory.RealWeil.continuous_omS_prod
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T19:16:53.262804+00:00
-- url     : https://prove2.me/theorems/833e7694-71d7-4582-81d7-bf27b1b56e27
-- title:
--   Real Weil: continuous om S prod
-- statement:
--   The Real Weil construction uses the continuous om S prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ContinuousMetaplecticSchwartzActionProd.lean#L11-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ContinuousMetaplecticSchwartzActionProd.lean#L11-L74

import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_MetaplecticRepresentation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IteratedLineDerivMemWeylAlg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsEqTransposeMulDiagonalMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousMetaplecticSchwartzActionProd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix Complex GlobalTheory.RealWeil
open scoped Real SchwartzMap ComplexConjugate
noncomputable section
open GlobalTheory GlobalTheory.RealWeil

theorem GlobalTheory.RealWeil.continuous_omS_prod (l : Type) [Fintype l] [DecidableEq l] (G : Type) [Group G] [TopologicalSpace G]
    (pr : G →* Matrix.symplecticGroup l ℝ) (om : G →* (L2 l ≃ₗᵢ[ℂ] L2 l)) (omS : G →* (Sch l →L[ℂ] Sch l))
    (hpr : Continuous pr) (hom : ∀ f : L2 l, Continuous fun g => om g f)
    (h3 : ∀ (g : G) (w : l ⊕ l → ℝ) (f : L2 l),
      om g (rho w f) = rho ((pr g : Matrix (l ⊕ l) (l ⊕ l) ℝ) *ᵥ w) (om g f))
    (h4 : ∀ (g : G) (f : Sch l), om g (f.toLp 2) = (omS g f).toLp 2) :
    Continuous fun x : G × Sch l => omS x.1 x.2 := by sorry
