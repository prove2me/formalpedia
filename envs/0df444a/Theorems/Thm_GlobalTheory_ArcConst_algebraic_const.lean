-- Prove2me | Theorems.Thm_GlobalTheory_ArcConst_algebraic_const
-- name    : GlobalTheory.ArcConst.algebraic_const
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T11:55:52.915646+00:00
-- url     : https://prove2.me/theorems/08f1d602-48eb-4efc-bf96-bab6942f0063
-- title:
--   Arc Const: algebraic const
-- statement:
--   The Arc Const construction uses the algebraic const property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/IsIntegralElemOfIsAlgebraicInt.lean#L119-L133
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/IsIntegralElemOfIsAlgebraicInt.lean#L119-L133

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_SectionOfLineBundleOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_IsIntegralElemOfIsAlgebraicInt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
noncomputable section
open GlobalTheory GlobalTheory.ArcConst
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem GlobalTheory.ArcConst.algebraic_const : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (K : Type) [Field K] [CharZero K], IsDomain (ArcS Dw K) ∧ Function.Injective (algebraMap (MvPolynomial (ArcLt Dw) (LaurentSeries K)) (ArcS Dw K)) ∧ (∀ s : ArcS Dw K, IsAlgebraic ℤ s → ∃ x : K, s = arcι Dw K (PowerSeries.C (R := K) x)) ∧ ∀ (F : Type) [Field F] [NumberField F] (f : F →+* ArcS Dw K), ∃ f₀ : F →+* K, f = ((arcι Dw K).comp (PowerSeries.C (R := K))).comp f₀ := by sorry
