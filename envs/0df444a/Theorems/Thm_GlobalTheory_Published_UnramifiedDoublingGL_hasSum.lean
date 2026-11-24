-- Prove2me | Theorems.Thm_GlobalTheory_Published_UnramifiedDoublingGL_hasSum
-- name    : GlobalTheory.Published.UnramifiedDoublingGL.hasSum
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T22:39:38.423071+00:00
-- url     : https://prove2.me/theorems/6883b610-5f4e-4136-a0d7-d9848d2023ee
-- title:
--   Unramified Doubling GL: has Sum
-- statement:
--   The Unramified Doubling GL construction uses the has Sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/TwistedTraceFormula/PairwiseDisjointCell.lean#L326-L343
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/TwistedTraceFormula/PairwiseDisjointCell.lean#L326-L343

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MemSiegelOfIffRightAct
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_T2SpaceGeneralLinearGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IwasawaBlockTriangular
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_NormalizedAbsCharacterization
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Cartan
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_PairwiseDisjointCell
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling Formalism.UG
open scoped NNReal Pointwise
open GlobalTheory GlobalTheory.Published
open GlobalTheory.GLDoubling

theorem GlobalTheory.Published.UnramifiedDoublingGL.hasSum (H : UnramifiedDoublingGL)
    (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k]
    (n : ℕ) [MeasurableSpace (GL (Fin n) k)] [BorelSpace (GL (Fin n) k)]
    (μ : Measure (GL (Fin n) k)) [μ.IsHaarMeasure] (hμ : μ (KO k (Fin n)) = 1)
    {ϖ : kˣ} (hϖ : valuation k (ϖ : k) = uniformizer k)
    {V : Type} [AddCommGroup V] [Module ℂ V] {π : Representation ℂ (GL (Fin n) k) V} {α : Fin n → ℂˣ}
    (hπ : HasSatake π α) {ω : GL (Fin n) k → ℂ} (hω : IsZonal π (KO k (Fin n)) ω) :
    ∃ s₀ : ℝ, ∀ s : ℂ, s₀ < s.re →
      HasSum (fun e : {e : Fin n → ℤ // Antitone e} => (μ.real (cell k (Fin n) ϖ e) : ℂ) *
          ((resCard k : ℂ) ^ (-((n : ℂ) / 2 + s) * ((∑ i, |e.1 i| : ℤ) : ℂ)) * ω (torusElt k (Fin n) ϖ e)))
        (lFactor (resCard k) α (s + 1 / 2) * lFactor (resCard k) α⁻¹ (s + 1 / 2) *
          invNormFactor (resCard k) n s) := by sorry
