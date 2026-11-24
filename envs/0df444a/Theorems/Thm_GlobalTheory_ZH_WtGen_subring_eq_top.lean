-- Prove2me | Theorems.Thm_GlobalTheory_ZH_WtGen_subring_eq_top
-- name    : GlobalTheory.ZH.WtGen.subring_eq_top
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T22:03:11.224707+00:00
-- url     : https://prove2.me/theorems/2dc49ffa-7df2-41d3-9afa-7b2868b6ac48
-- title:
--   Wt Gen: subring eq top
-- statement:
--   The Wt Gen construction uses the subring eq top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/PureSectionRatiosGenerateFunctions.lean#L42-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/PureSectionRatiosGenerateFunctions.lean#L42-L55

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PullChartIsLB
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsUniqueIsRatio
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_IsPartPartSec
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_GroupAlgebraSingleOneMemOfSpan
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsPowEqTorus
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_PureSectionRatiosGenerateFunctions
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
open GlobalTheory GlobalTheory.ZH GlobalTheory.ZH.WtGen
open GlobalTheory.ZH.WtPart
variable {A R X : Type} [CommRing A] [CommRing R] [AddCommGroup X]
  {f : A →+* R} {m : Multiplicative X →* R}
  (hb : Function.Bijective (AddMonoidAlgebra.liftNCRingHom f m (fun _ _ => Commute.all _ _)))
include hb

theorem GlobalTheory.ZH.WtGen.subring_eq_top {I : Type} (e : Module.Basis I ℤ X) (S : Subring R) (h0 : ∀ a, f a ∈ S)
    (h : ∀ i, Ideal.span {a : A | f a * m (Multiplicative.ofAdd (e i)) ∈ S} = ⊤ ∧
      Ideal.span {a : A | f a * m (Multiplicative.ofAdd (-e i)) ∈ S} = ⊤) : S = ⊤ := by sorry
