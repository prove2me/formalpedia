-- Prove2me | Theorems.Thm_LocalConjugacy_Proof_LocalConjugacy_nilpotent_coprime_split
-- name    : LocalConjugacy.Proof.LocalConjugacy.nilpotent_coprime_split
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-09-30T16:26:06.92057+00:00
-- url     : https://prove2.me/theorems/bddf0c26-9307-4cca-9032-0513b883f5f7
-- title:
--   Coprime characteristic factors of a finite nilpotent group
-- statement:
--   Let $G$ be a finite nilpotent group that is not a $p$-group for any prime $p$. Then there are characteristic subgroups $A,B\le G$ such that
--
--   $$G=AB,\qquad A\cap B=\{1\},\qquad \gcd(|A|,|B|)=1,\qquad A\ne\{1\},\quad B\ne\{1\}.$$
--
--   Thus $G$ splits into nontrivial complementary characteristic factors of coprime orders. This supports reduction of nilpotent coefficients to smaller characteristic factors.
-- source:
--   Michael C. Burkhart, Local conjugacy in prosolvable groups, https://arxiv.org/abs/2609.37678; supporting formalization lemma, LocalConjugacy/NilpotentCoprimeFactors.lean, lines 49–68; source SHA-256 218aa772d0c3d92cbfcc6e44cffcfc39ddfd67473917973c99c5f2f64738ffc2.

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

universe u_1

theorem LocalConjugacy.Proof.LocalConjugacy.nilpotent_coprime_split :
∀ {G : Type u_1} [inst : Group.{u_1} G] [Finite.{u_1 + 1} G] [@Group.IsNilpotent.{u_1} G inst]
  (h : Not (@Exists.{1} Nat fun (p : Nat) => And (Nat.Prime p) (@IsPGroup.{u_1} p G inst))),
  @Exists.{u_1 + 1} (@Subgroup.{u_1} G inst) fun (A : @Subgroup.{u_1} G inst) =>
    @Exists.{u_1 + 1} (@Subgroup.{u_1} G inst) fun (B : @Subgroup.{u_1} G inst) =>
      And (@Subgroup.Characteristic.{u_1} G inst A)
        (And (@Subgroup.Characteristic.{u_1} G inst B)
          (And (@Subgroup.IsComplement'.{u_1} G inst A B)
            (And
              (Nat.Coprime
                (Nat.card.{u_1}
                  (@Subtype.{u_1 + 1} G fun (x : G) =>
                    @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                      (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                        (@Subgroup.instSetLike.{u_1} G inst))
                      A x))
                (Nat.card.{u_1}
                  (@Subtype.{u_1 + 1} G fun (x : G) =>
                    @Membership.mem.{u_1, u_1} G (@Subgroup.{u_1} G inst)
                      (@SetLike.instMembership.{u_1, u_1} (@Subgroup.{u_1} G inst) G
                        (@Subgroup.instSetLike.{u_1} G inst))
                      B x)))
              (And
                (@Ne.{u_1 + 1} (@Subgroup.{u_1} G inst) A
                  (@Bot.bot.{u_1} (@Subgroup.{u_1} G inst) (@Subgroup.instBot.{u_1} G inst)))
                (@Ne.{u_1 + 1} (@Subgroup.{u_1} G inst) B
                  (@Bot.bot.{u_1} (@Subgroup.{u_1} G inst) (@Subgroup.instBot.{u_1} G inst))))))) := by sorry
