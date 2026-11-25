-- Prove2me | Theorems.Thm_GlobalTheory_Reg_Transfer_regular_at_centre
-- name    : GlobalTheory.Reg.Transfer.regular_at_centre
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T19:18:19.167817+00:00
-- url     : https://prove2.me/theorems/f7001ace-5cf1-4dd6-a430-74ed5f0a8709
-- title:
--   Transfer: regular at centre
-- statement:
--   The Transfer construction uses the regular at centre property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GenericRegularity/RegularAtCentre.lean#L243-L254
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GenericRegularity/RegularAtCentre.lean#L243-L254

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_RegularCharts_SCharts
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RegModelC
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GenericRegularity_RegularAtCentre
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.Reg GlobalTheory.Reg.Transfer
open IsLocalRing Formalism.L2.Pj GlobalTheory.Reg

theorem GlobalTheory.Reg.Transfer.regular_at_centre {O A : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (maximalIdeal O) O] [CharZero O]
    [CommRing A] [IsDomain A] [Algebra O A] [Algebra.FiniteType O A] [Module.Flat O A]
    [IsIntegrallyClosed A] (g : FractionRing A) (x : A) (hx0 : x ≠ 0)
    (hpts : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Algebra O V]
      [Module.Finite O V] (φ : A →ₐ[O] V), φ x ≠ 0 →
        ∃ (e : ℕ) (r : EReal), 0 < e ∧ ChV φ.toRingHom e g r ∧ 0 ≤ r)
    (qq : Ideal A) [qq.IsPrime] (hqq : qq ⊔ Ideal.map (algebraMap O A) (maximalIdeal O) ≠ ⊤) :
    ∃ a s : A, s ∉ qq ∧ g * algebraMap A (FractionRing A) s = algebraMap A (FractionRing A) a := by sorry
