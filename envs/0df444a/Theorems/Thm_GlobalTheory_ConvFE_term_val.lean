-- Prove2me | Theorems.Thm_GlobalTheory_ConvFE_term_val
-- name    : GlobalTheory.ConvFE.term_val
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T17:06:13.144739+00:00
-- url     : https://prove2.me/theorems/86965ead-1bc7-5864-8196-4485959cb769
-- title:
--   Conv FE: term val
-- statement:
--   The Conv FE construction uses the term val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/SvalSecScale.lean#L108-L121
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/SvalSecScale.lean#L108-L121

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_WCompat
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueSamePt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_SvalTwistOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ValuesNatural
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_AdicSumRel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ConvTermFe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_SecRelationDescends
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_RelationOfFiniteLevels
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsGenT
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_SvalSecScale
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
noncomputable section
open GlobalTheory GlobalTheory.ConvFE
open ReciprocityTheory.ChartRestriction.G.DVR
variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F]

theorem GlobalTheory.ConvFE.term_val {W : Type} [CommRing W] [Algebra R W] {φ : TF (R := R) F ⟶ TA R W} {k l : ℕ}
    {f : ∀ α, SecBT D (TA R W) k α} {g : ∀ α, SecBT D (TA R W) l α} {s : Raw D F k} {s' : Raw D F l}
    (hf : PullB D F φ k f s) (hg : PullB D F φ l g s') (a a' : Multiplicative D.X →* Wˣ) {β ga α : D.X}
    {p : SecBT D (TA R W) (k + l) α} (hp : IsProdB (twist a f β) (twist a' g ga) p)
    {Z : Over (Spec (CommRingCat.of R))} (r : Z ⟶ DegPre.BF D F) (z : Z.left) {J} (hJ : Good D.P.L z J) :
    sval p (r ≫ φ ▷ D.P.A).left z J =
      cst (R := W) (r ≫ fst _ _ ≫ φ).left z (a (Multiplicative.ofAdd β) * a' (Multiplicative.ofAdd ga)).val *
        (sval (s β) r.left z J * sval (s' ga) r.left z J *
          (cubV D.cub z J (toUnit Z ≫ D.c β) (toUnit Z ≫ D.c ga) (r ≫ snd _ _)).val) := by sorry
