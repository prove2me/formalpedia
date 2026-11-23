-- Prove2me | Theorems.Thm_GlobalTheory_ZH_WtLin_coeff_symm_sum
-- name    : GlobalTheory.ZH.WtLin.coeff_symm_sum
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:13:27.271602+00:00
-- url     : https://prove2.me/theorems/7e265787-14c9-4ef5-ab39-0de41623ecb8
-- title:
--   Wt Lin: coeff symm sum
-- statement:
--   The Wt Lin construction uses the coeff symm sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/CoeffSymmSum.lean#L11-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/CoeffSymmSum.lean#L11-L23

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PullChartIsLB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_CoeffSymmSum
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra
noncomputable section
open GlobalTheory GlobalTheory.ZH GlobalTheory.ZH.WtLin

theorem GlobalTheory.ZH.WtLin.coeff_symm_sum {A B X : Type} [CommRing A] [CommRing B] [AddCommGroup X] (f : A →+* B)
    (g : Multiplicative X →* B) (hc : ∀ x y, Commute (f x) (g y))
    (hb : Function.Bijective (AddMonoidAlgebra.liftNCRingHom f g hc)) {J : Type} [Fintype J]
    (c : J → A) (s : J → B) (χ : X) :
    ((Equiv.ofBijective _ hb).symm (∑ i, f (c i) * s i)).coeff χ =
      ∑ i, c i * ((Equiv.ofBijective _ hb).symm (s i)).coeff χ := by sorry
