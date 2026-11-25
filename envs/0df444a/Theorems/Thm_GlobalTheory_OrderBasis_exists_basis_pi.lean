-- Prove2me | Theorems.Thm_GlobalTheory_OrderBasis_exists_basis_pi
-- name    : GlobalTheory.OrderBasis.exists_basis_pi
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T07:44:43.677505+00:00
-- url     : https://prove2.me/theorems/3e42f4e0-a1c4-44ac-b6b7-b3c7da00b0c7
-- title:
--   Order Basis: exists basis pi
-- statement:
--   The Order Basis construction uses the exists basis pi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsBasisFgMaximalOrderSpanningFree.lean#L10-L110
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/ExistsBasisFgMaximalOrderSpanningFree.lean#L10-L110

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

theorem GlobalTheory.OrderBasis.exists_basis_pi {E : Type} [CommRing E] (R : Subring E) [IsPrincipalIdealRing R]
    (s t : E) (hs : IsUnit s) (ht : IsUnit t) :
    ∀ (m : ℕ) (Q : Submodule R (Fin m → E)), (∀ q ∈ Q, ∀ i, s * q i ∈ R) →
      (∀ i, (Pi.single i t : Fin m → E) ∈ Q) →
      ∃ b : Fin m → Fin m → E, LinearIndependent E b ∧ Q = Submodule.span R (Set.range b) := by sorry
