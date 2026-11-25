-- Prove2me | Theorems.Thm_GlobalTheory_OrderBasis_exists_basis
-- name    : GlobalTheory.OrderBasis.exists_basis
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T07:42:27.250462+00:00
-- url     : https://prove2.me/theorems/c2a7653f-72ec-4441-acf0-d2420cbc220a
-- title:
--   Order Basis: exists basis
-- statement:
--   The Order Basis construction uses the exists basis property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsBasisFgMaximalOrderSpanningFree.lean#L120-L181
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsBasisFgMaximalOrderSpanningFree.lean#L120-L181

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

theorem GlobalTheory.OrderBasis.exists_basis {E : Type} [CommRing E] (R : Subring E) [IsPrincipalIdealRing R]
    (hD : ∀ x : E, ∃ d ∈ R, IsUnit d ∧ d * x ∈ R) {V : Type} [AddCommGroup V] [Module E V]
    {m : ℕ} (y : Fin m → V) (hy : LinearIndependent E y) (Q : Submodule R V) (hQ : Q.FG)
    (hs : Submodule.span E (Q : Set V) = Submodule.span E (Set.range y)) :
    ∃ b : Fin m → V, LinearIndependent E b ∧ Q = Submodule.span R (Set.range b) := by sorry
