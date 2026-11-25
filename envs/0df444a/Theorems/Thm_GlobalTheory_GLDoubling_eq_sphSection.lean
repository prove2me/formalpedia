-- Prove2me | Theorems.Thm_GlobalTheory_GLDoubling_eq_sphSection
-- name    : GlobalTheory.GLDoubling.eq_sphSection
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T12:11:05.967857+00:00
-- url     : https://prove2.me/theorems/061cd12e-ff1e-587f-a784-3aee1f39fa16
-- title:
--   GLDoubling: eq sph Section
-- statement:
--   The GLDoubling construction uses the eq sph Section property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/TwistedTraceFormula/PairwiseDisjointCell.lean#L119-L123
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/TwistedTraceFormula/PairwiseDisjointCell.lean#L119-L123

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

theorem GlobalTheory.GLDoubling.eq_sphSection {s : ℂ} {Φ : GL (n ⊕ n) k → ℂ} (h1 : Φ 1 = 1)
    (hl : ∀ (p : siegel k n) h, Φ (p * h) = npow (absRatio k n p) (s + (Fintype.card n : ℂ) / 2) * Φ h)
    (hr : ∀ h, ∀ κ ∈ KO k (n ⊕ n), Φ (h * κ) = Φ h) : Φ = sphSection k n s := by sorry
