-- Prove2me | Theorems.Thm_LocalConjugacy_Proof_LocalConjugacy_sylowPro_map
-- name    : LocalConjugacy.Proof.LocalConjugacy.sylowPro_map
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-09-30T16:22:04.586855+00:00
-- url     : https://prove2.me/theorems/58667443-1fae-4595-b507-4efdbdeaf7aa
-- title:
--   Continuous images of Sylow pro-$p$ subgroups
-- statement:
--   Let $G$ and $F$ be profinite groups, let $p$ be prime, and let $H\le G$ be closed. If $P$ is a Sylow pro-$p$ subgroup of $H$ and $f:G\to F$ is a continuous homomorphism, then
--
--   $$f(P)\text{ is a Sylow pro-}p\text{ subgroup of }f(H).$$
--
--   Here a Sylow pro-$p$ subgroup is a maximal closed pro-$p$ subgroup. This transports Sylow data through continuous homomorphisms, including quotient maps.
-- source:
--   Michael C. Burkhart, Local conjugacy in prosolvable groups, https://arxiv.org/abs/2609.37678; supporting formalization lemma, LocalConjugacy/ProfiniteQuotients.lean, lines 43–56; source SHA-256 ff4a2c1178557f4150ace6a6d2f4bef33f40f1fe2881cbf07c786cf6270d5899.

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

theorem LocalConjugacy.Proof.LocalConjugacy.sylowPro_map :
∀ {G : Type u_1} {F : Type u_2} [inst : Group.{u_1} G] [inst_1 : Group.{u_2} F] [inst_2 : TopologicalSpace.{u_1} G]
  [inst_3 : TopologicalSpace.{u_2} F] [@LocalConjugacy.Proof.LocalConjugacy.Profinite.{u_1} G inst inst_2]
  [@LocalConjugacy.Proof.LocalConjugacy.Profinite.{u_2} F inst_1 inst_3] {p : Nat} [Fact (Nat.Prime p)]
  (H P : @Subgroup.{u_1} G inst)
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
