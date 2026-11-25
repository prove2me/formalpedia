-- Prove2me | Theorems.Thm_GlobalTheory_HL_encard_orbit_fiber
-- name    : GlobalTheory.HL.encard_orbit_fiber
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T05:15:43.376551+00:00
-- url     : https://prove2.me/theorems/5d5497e7-a683-57f2-aabf-4b1de36454e9
-- title:
--   HL: encard orbit fiber
-- statement:
--   The HL construction uses the encard orbit fiber property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/MassOrbitsEqTsumFiber.lean#L25-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/MassOrbitsEqTsumFiber.lean#L25-L53

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsHermND
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_InvVolMulPosLeConj
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_MassOrbitsEqTsumFiber
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
open GlobalTheory GlobalTheory.HL

theorem GlobalTheory.HL.encard_orbit_fiber {G X Y : Type*} [Group G] [MulAction G X] [MulAction G Y]
    (H : Subgroup G) (P : X → Prop) (π : X → Y)
    (hP : ∀ h ∈ H, ∀ x, P x → P (h • x) ∧ π (h • x) = h • π x) (x : X) (hx : P x)
    (hfin : (H ⊓ MulAction.stabilizer G x).relIndex (H ⊓ MulAction.stabilizer G (π x)) ≠ 0) :
    ({z | (Quotient.mk'' z : MulAction.orbitRel.Quotient H X) = Quotient.mk'' x ∧
        P z ∧ π z = π x} : Set X).encard
      = (H ⊓ MulAction.stabilizer G x).relIndex (H ⊓ MulAction.stabilizer G (π x)) := by sorry
