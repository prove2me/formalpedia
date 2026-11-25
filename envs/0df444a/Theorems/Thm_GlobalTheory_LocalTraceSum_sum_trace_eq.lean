-- Prove2me | Theorems.Thm_GlobalTheory_LocalTraceSum_sum_trace_eq
-- name    : GlobalTheory.LocalTraceSum.sum_trace_eq
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T12:20:22.73157+00:00
-- url     : https://prove2.me/theorems/5a24dd20-d338-4eeb-b2d0-b5d7d870d440
-- title:
--   Local Trace Sum: sum trace eq
-- statement:
--   The Local Trace Sum construction uses the sum trace eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/TraceEqSumLocalTracesAbovePrime.lean#L187-L236
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/TraceEqSumLocalTracesAbovePrime.lean#L187-L236

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_PsiEDef
import Definitions.Def_Formalism_LocalRingCardinality_DataSpaces
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_TraceEqSumLocalTracesAbovePrime
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain Formalism.MainNotions.S.Loc ValuativeRel
open scoped nonZeroDivisors
open GlobalTheory GlobalTheory.LocalTraceSum
open Filter Topology TensorProduct

theorem GlobalTheory.LocalTraceSum.sum_trace_eq : ∀ {F : Type} [Field F] [NumberField F] (l : ℕ) [Fact l.Prime] (S : Finset (HeightOneSpectrum (𝓞 F))), (∀ p, p ∈ S ↔ (l : 𝓞 F) ∈ p.asIdeal) → ∀ (K : S → Type) [∀ p, Field (K p)] [∀ p, Algebra ℚ_[l] (K p)] [∀ p, FiniteDimensional ℚ_[l] (K p)] [∀ p, ValuativeRel (K p)] [∀ p, TopologicalSpace (K p)] (ι : ∀ p, F →+* K p), (∀ p, IsNonarchimedeanLocalField (K p)) → (∀ p, Continuous (algebraMap ℚ_[l] (K p))) → (∀ p, DenseRange (ι p)) → (∀ p (x y : F), (ι p x ≤ᵥ ι p y) ↔ p.1.valuation F x ≤ p.1.valuation F y) → ∀ a : F, ∑ p, Algebra.trace ℚ_[l] (K p) (ι p a) = ((Algebra.trace ℚ F a : ℚ) : ℚ_[l]) := by sorry
