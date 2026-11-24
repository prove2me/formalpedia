-- Prove2me | Theorems.Thm_GlobalTheory_SmGL_InductionContragredient_lower
-- name    : GlobalTheory.SmGL.InductionContragredient.lower
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T20:17:39.972329+00:00
-- url     : https://prove2.me/theorems/fa4b9dbe-037e-42cc-aca7-110f0d153422
-- title:
--   Induction Contragredient: lower
-- statement:
--   The Induction Contragredient construction uses the lower property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/TwistedTraceFormula/HasFiniteLengthOfIsIrreducible.lean#L135-L149
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/TwistedTraceFormula/HasFiniteLengthOfIsIrreducible.lean#L135-L149

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsUnitarisableOfCharIff
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_LeviEmbMemNormalizerLower
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_T2SpaceGeneralLinearGroup
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_HasFiniteLengthOfIsIrreducible
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL
open GlobalTheory
open GlobalTheory.SmGL
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)]
  [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n]
  {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem GlobalTheory.SmGL.InductionContragredient.lower (h : InductionContragredient k) (e : (Σ a, m a) ≃ n)
    [MeasurableSpace (GL n k)] [BorelSpace (GL n k)] (μ : Measure (GL n k)) [μ.IsHaarMeasure]
    {ρ : Representation ℂ (Levi k m) W} (hρ : IsSmooth ρ) :
    ∃ Φ : (parIndLower e (contra ρ)).Equiv (contra (parIndLower e ρ)),
      ∀ (f' : IndSpLower e (contra ρ)) (f : IndSpLower e ρ),
        (Φ f' : Module.Dual ℂ (IndSpLower e ρ)) f =
          ∫ x in (KO k n : Set (GL n k)), (f'.1.1 x : Module.Dual ℂ W) (f.1.1 x) ∂μ := by sorry
