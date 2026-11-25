-- Prove2me | Theorems.Thm_GlobalTheory_WittQuot_teichmuller_quot
-- name    : GlobalTheory.WittQuot.teichmuller_quot
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T16:42:23.299743+00:00
-- url     : https://prove2.me/theorems/ff3b752f-9191-4eea-b7c3-ff30cb068cd7
-- title:
--   Witt Quot: teichmuller quot
-- statement:
--   The Witt Quot construction uses the teichmuller quot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/TeichmullerQuot.lean#L44-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/TeichmullerQuot.lean#L44-L79

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_Imports
import Definitions.Def_ReciprocityTheory_DualLattices_CyclicRecursion
import Definitions.Def_ReciprocityTheory_DualLattices_TowerZeroSurjective
import Definitions.Def_ReciprocityTheory_DualLattices_LinPairStatement
import Definitions.Def_ReciprocityTheory_DualLattices_SubMemOfCompat
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_LePreimageOfNil
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_TeichmullerQuot
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct IsLocalRing Matrix CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2 ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.WittQuot

theorem GlobalTheory.WittQuot.teichmuller_quot :
  (∀ (p : ℕ) [Fact p.Prime] {C : Type} [Field C] [IsAlgClosed C] [CharZero C] {v : Valuation C NNReal} (O : Type) [CommRing O] [Algebra O C]
    [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] (hv : v.Integers O) (ε : PreTilt O p)
    (hε : IsPrimitiveRoot (((frobeniusEquiv (PreTilt O p) p).symm ε).untilt) p) (ϖ : PreTilt O p), ϖ.untilt = (p : O) →
    ∀ (W : Type) [CommRing W] (pr : Ainf.A p O →+* W), Function.Surjective pr →
    RingHom.ker pr = Ideal.span {(p : Ainf.A p O) ^ 2, WittVector.teichmuller p ϖ} →
    (∀ w : W, ∃ c : PreTilt O p, ∃ c' : W, w = pr (WittVector.teichmuller p c) + p * c') ∧
    (∀ (n : ℕ) (a : Fin n → PreTilt O p), ∑ j, pr (WittVector.teichmuller p (a j)) = pr (WittVector.teichmuller p (∑ j, a j)) +
      p * pr (WittVector.teichmuller p (MvPolynomial.eval₂ (Int.castRingHom (PreTilt O p)) (fun j => (frobeniusEquiv (PreTilt O p) p).symm (a j)) (wS p n)))) ∧
    (∀ c : PreTilt O p, WittVector.fontaineTheta O p (WittVector.teichmuller p c) ∈ Ideal.span {(p : O)} → pr (WittVector.teichmuller p c) = 0)) := by sorry
