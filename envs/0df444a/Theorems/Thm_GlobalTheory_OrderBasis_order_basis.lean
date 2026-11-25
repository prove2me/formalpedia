-- Prove2me | Theorems.Thm_GlobalTheory_OrderBasis_order_basis
-- name    : GlobalTheory.OrderBasis.order_basis
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T06:09:23.480082+00:00
-- url     : https://prove2.me/theorems/6b65e8ef-3c9c-40e8-ad3e-11073c3529c7
-- title:
--   Order Basis: order basis
-- statement:
--   The Order Basis construction uses the order basis property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsBasisFgMaximalOrderSpanningFree.lean#L183-L194
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsBasisFgMaximalOrderSpanningFree.lean#L183-L194

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_IsPrincipalIdealRingOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExistsBasisFgMaximalOrderSpanningFree
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
open GlobalTheory GlobalTheory.OrderBasis

theorem GlobalTheory.OrderBasis.order_basis : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ {n m : ℕ} (y : Fin m → Fin n → E), LinearIndependent E y → ∀ Q : Submodule L.O (Fin n → E), Q.FG → Submodule.span E (Q : Set (Fin n → E)) = Submodule.span E (Set.range y) → ∃ b : Fin m → Fin n → E, LinearIndependent E b ∧ Q = Submodule.span L.O (Set.range b) := by sorry
