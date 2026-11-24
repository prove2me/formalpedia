-- Prove2me | Theorems.Thm_GlobalTheory_GLDoubling_hasSum_cell
-- name    : GlobalTheory.GLDoubling.hasSum_cell
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T13:44:17.837093+00:00
-- url     : https://prove2.me/theorems/66e790be-abf1-4c05-bd7d-4e1e73ceefc9
-- title:
--   GLDoubling: has Sum cell
-- statement:
--   The GLDoubling construction uses the has Sum cell property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/TwistedTraceFormula/PairwiseDisjointCell.lean#L277-L292
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/TwistedTraceFormula/PairwiseDisjointCell.lean#L277-L292

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
open GlobalTheory GlobalTheory.GLDoubling
variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  (n : Type) [Fintype n] [DecidableEq n]
variable {k n}

theorem GlobalTheory.GLDoubling.hasSum_cell {N : ℕ} [MeasurableSpace (GL (Fin N) k)] [BorelSpace (GL (Fin N) k)]
    (μ : Measure (GL (Fin N) k)) {ϖ : kˣ} (hϖ : valuation k (ϖ : k) = uniformizer k) {f : GL (Fin N) k → ℂ}
    (hf : Integrable f μ) (hb : ∀ g, ∀ x ∈ KO k (Fin N), ∀ y ∈ KO k (Fin N), f (x * g * y) = f g) :
    HasSum (fun e : {e : Fin N → ℤ // Antitone e} =>
      (μ.real (cell k (Fin N) ϖ e) : ℂ) * f (torusElt k (Fin N) ϖ e)) (∫ g, f g ∂μ) := by sorry
