-- Prove2me | Theorems.Thm_LocalConjugacy_Proof_LocalConjugacy_sylowPro_map_finite
-- name    : LocalConjugacy.Proof.LocalConjugacy.sylowPro_map_finite
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-09-30T15:52:39.734722+00:00
-- url     : https://prove2.me/theorems/d1902759-c46b-4925-bfe2-0f158bb1e7f3
-- title:
--   Finite images of Sylow pro-subgroups
-- statement:
--   Let $G$ be profinite, let $F$ be a finite discrete group, and let $f:G\to F$ be a continuous homomorphism. Let $p$ be prime, let $H\le G$ be closed, and let $P$ be a Sylow pro-$p$ subgroup of $H$, meaning a closed subgroup maximal among closed pro-$p$ subgroups of $H$. Then
--
--   $$f(P)\text{ is a Sylow pro-}p\text{ subgroup of }f(H).$$
--
--   Since $F$ is finite and discrete, the conclusion is equivalently that $f(P)$ is an ordinary Sylow $p$-subgroup of $f(H)$. This passes Sylow data to finite quotients.
-- source:
--   Michael C. Burkhart, Local conjugacy in prosolvable groups, https://arxiv.org/abs/2609.37678; supporting formalization lemma, LocalConjugacy/SylowFiniteImages.lean, lines 30–49; source SHA-256 fcdafbc9260ef612c6eddfb6a97ef990da3d35c0a692ff7c2c596cf6f0547661.

import Definitions.Def_LocalConjugacy_Groups
import Definitions.Def_LocalConjugacy_Cohomology
import Definitions.Def_LocalConjugacy_Examples
import Definitions.Def_LocalConjugacy_Proof_Definitions
import Definitions.Def_LocalConjugacy_Proof_Bridges
import Definitions.Def_LocalConjugacy_Proof_Counterexamples_Heisenberg
import Definitions.Def_LocalConjugacy_Proof_Counterexamples_HeisenbergStructure
import Definitions.Def_LocalConjugacy_Proof_Counterexamples_HeisenbergSupersolvable
import Definitions.Def_LocalConjugacy_Proof_ConcreteGroups
import Definitions.Def_LocalConjugacy_Targets
import Definitions.Def_LocalConjugacy_Proof_Compactness
import Definitions.Def_LocalConjugacy_Proof_ProfiniteSylow
import Definitions.Def_LocalConjugacy_Proof_StructuralImages
import Definitions.Def_LocalConjugacy_Proof_FiniteAbelianCohomology
import Definitions.Def_LocalConjugacy_Proof_AbelianComplement
import Definitions.Def_LocalConjugacy_Proof_QuotientReduction
import Definitions.Def_LocalConjugacy_Proof_Cohomology
import Definitions.Def_LocalConjugacy_Proof_InvariantRestriction
import Definitions.Def_LocalConjugacy_Proof_CocycleActions
import Definitions.Def_LocalConjugacy_Proof_CoprimeCohomology
import Definitions.Def_LocalConjugacy_Proof_CocycleDescent
import Definitions.Def_LocalConjugacy_Proof_CocycleZorn
import Definitions.Def_LocalConjugacy_Proof_CocycleProducts
import Definitions.Def_LocalConjugacy_Proof_FiniteCoefficientSubgroup
import Definitions.Def_LocalConjugacy_Proof_CocycleInvarianceSubgroup
import Definitions.Def_LocalConjugacy_Proof_CocycleInjectivity
import Definitions.Def_LocalConjugacy_Proof_CocycleRebase
import Definitions.Def_LocalConjugacy_Proof_FiniteHall
import Definitions.Def_LocalConjugacy_Proof_SupersolvableStructure
import Definitions.Def_LocalConjugacy_Proof_ProfiniteHall
import Definitions.Def_LocalConjugacy_Proof_ActionProductTopology
import Definitions.Def_LocalConjugacy_Proof_HallCohomology
import Definitions.Def_LocalConjugacy_Proof_SupersolvableRestriction
import Definitions.Def_LocalConjugacy_Proof_NilpotentCoefficients
import Definitions.Def_LocalConjugacy_Proof_NonabelianComplement
import Definitions.Def_LocalConjugacy_Proof_ComplementSupersolvable
import Definitions.Def_LocalConjugacy_Proof_Counterexamples_Quaternion
import Definitions.Def_LocalConjugacy_Proof_QuaternionCohomology
import Definitions.Def_LocalConjugacy_Proof_QuaternionMatrices
import Definitions.Def_LocalConjugacy_Proof_QuaternionAction
import Definitions.Def_LocalConjugacy_Proof_QuaternionComplements

universe u_1 u_2

theorem LocalConjugacy.Proof.LocalConjugacy.sylowPro_map_finite :
∀ {G : Type u_1} {F : Type u_2} [inst : Group.{u_1} G] [inst_1 : Group.{u_2} F] [inst_2 : TopologicalSpace.{u_1} G]
  [inst_3 : TopologicalSpace.{u_2} F] [@LocalConjugacy.Proof.LocalConjugacy.Profinite.{u_1} G inst inst_2]
  [Finite.{u_2 + 1} F] [@DiscreteTopology.{u_2} F inst_3] {p : Nat} [Fact (Nat.Prime p)] (H P : @Subgroup.{u_1} G inst)
  (hH :
    @IsClosed.{u_1} G inst_2
      (@SetLike.coe.{u_1, u_1} (@Subgroup.{u_1} G inst) G (@Subgroup.instSetLike.{u_1} G inst) H))
  (hP : @LocalConjugacy.Proof.LocalConjugacy.IsSylowPro.{u_1} p G inst inst_2 H P)
  (f :
    @MonoidHom.{u_1, u_2} G F
      (@MulOneClass.toMulOne.{u_1} G
        (@Monoid.toMulOneClass.{u_1} G (@DivInvMonoid.toMonoid.{u_1} G (@Group.toDivInvMonoid.{u_1} G inst))))
      (@MulOneClass.toMulOne.{u_2} F
        (@Monoid.toMulOneClass.{u_2} F (@DivInvMonoid.toMonoid.{u_2} F (@Group.toDivInvMonoid.{u_2} F inst_1)))))
  (hf :
    @Continuous.{u_1, u_2} G F inst_2 inst_3
      (@DFunLike.coe.{max (u_1 + 1) (u_2 + 1), u_1 + 1, u_2 + 1}
        (@MonoidHom.{u_1, u_2} G F
          (@MulOneClass.toMulOne.{u_1} G
            (@Monoid.toMulOneClass.{u_1} G (@DivInvMonoid.toMonoid.{u_1} G (@Group.toDivInvMonoid.{u_1} G inst))))
          (@MulOneClass.toMulOne.{u_2} F
            (@Monoid.toMulOneClass.{u_2} F (@DivInvMonoid.toMonoid.{u_2} F (@Group.toDivInvMonoid.{u_2} F inst_1)))))
        G (fun (x : G) => F)
        (@MonoidHom.instFunLike.{u_1, u_2} G F
          (@MulOneClass.toMulOne.{u_1} G
            (@Monoid.toMulOneClass.{u_1} G (@DivInvMonoid.toMonoid.{u_1} G (@Group.toDivInvMonoid.{u_1} G inst))))
          (@MulOneClass.toMulOne.{u_2} F
            (@Monoid.toMulOneClass.{u_2} F (@DivInvMonoid.toMonoid.{u_2} F (@Group.toDivInvMonoid.{u_2} F inst_1)))))
        f)),
  @LocalConjugacy.Proof.LocalConjugacy.IsSylowPro.{u_2} p F inst_1 inst_3 (@Subgroup.map.{u_1, u_2} G inst F inst_1 f H)
    (@Subgroup.map.{u_1, u_2} G inst F inst_1 f P) := by sorry
