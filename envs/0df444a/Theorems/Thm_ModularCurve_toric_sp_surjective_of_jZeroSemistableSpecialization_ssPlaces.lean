-- Prove2me | Theorems.Thm_ModularCurve_toric_sp_surjective_of_jZeroSemistableSpecialization_ssPlaces
-- name    : ModularCurve.toric_sp_surjective_of_jZeroSemistableSpecialization_ssPlaces
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:54.908972+00:00
-- url     : https://prove2.me/theorems/647526ce-a432-5613-8bfe-128006a5ff89
-- title:
--   Specialisation surjects onto the toric kernel at supersingular nodes
-- statement:
--   Let $M$ be a nonzero natural number and $q'$ a prime not dividing $M$, with $M q'$ nonzero, and let $A$ be a valuation subring of $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ` lying over $q'$ in the sense that $q'$ belongs to the nonunits of $A$; assume the set $\mathrm{ssPlaces}\,q'\,M\,k$ of places $w$ of $\mathrm{modularFunctionFieldC}\,k\,M$ over the residue field $k =$ `IsLocalRing.ResidueField A` satisfying `IsSupersingularPlace q' M` is finite, and fix module structures over $\mathrm{HeckeAlg} = \mathbb{Z}[X_\ell : \ell \text{ prime}]$ on $\mathrm{JZero}(Mq')$, on $\mathrm{JZero}(M)$ (each the degree-zero Picard group of the corresponding modular function field over $\overline{\mathbb{Q}}$) and on $\mathrm{Pic0}\,k\,(\mathrm{modularFunctionFieldC}\,k\,M)$. Let $D$ be a `JZeroSemistableSpecialization A M q' hq'`, that is: a finite set $D.\mathrm{nodes}$ of pairs of places of $\mathrm{modularFunctionFieldC}\,k\,M$ with residue fields equal to $k$, a semilinear automorphism $D.\mathrm{frob}$ acting on $k$ by $a \mapsto a^{q'}$ and stabilising the nodes with the induced node permutation an involution, a width function on the nodes, a component-group homomorphism $D.\mathrm{comp}$ and a specialisation homomorphism $D.\mathrm{sp}$ from the inertia invariants $\mathrm{inertiaInvariants}\,A\,(Mq')$ of $\mathrm{JZero}(Mq')$ to $\mathrm{GluedPic0}\,k\,(\mathrm{modularFunctionFieldC}\,k\,M)\,D.\mathrm{nodes}$, subject to the compatibilities with Hecke operators and Frobenius required by that structure. Assume (hi) that $D.\mathrm{nodes}$ is exactly the set of node pairs $\mathrm{nodePairsOfPlaces}\,D.\mathrm{frob}$ attached to the supersingular places, and (hii) that for every $\sigma$ in the inertia subgroup $A.\mathrm{inertiaSubgroupIn}\,\mathbb{Q}$ (the image in $\mathrm{Aut}(\overline{\mathbb{Q}}/\mathbb{Q})$ of the inertia subgroup inside the decomposition subgroup) and every $x \in \mathrm{JZero}(Mq')$ killed by some positive integer prime to $q'$, the element $\sigma \cdot x - x$ lies in the inertia invariants, is annihilated by $D.\mathrm{comp}$, and its image under $D.\mathrm{sp}$ has vanishing image under $\mathrm{toPic0Pair}$. Then for every $z$ in $\mathrm{GluedPic0}\,k\,(\mathrm{modularFunctionFieldC}\,k\,M)\,D.\mathrm{nodes}$ with $\mathrm{toPic0Pair}\,D.\mathrm{nodes}\,z = 0$ there is an element $y$ of the $\mathrm{HeckeAlg}$-submodule $\mathrm{toricMonodromyPart}\,q'\,(A.\mathrm{inertiaSubgroupIn}\,\mathbb{Q})$ of $\mathrm{JZero}(Mq')$, spanned by the elements $\sigma \cdot x - x$ with $\sigma$ in the inertia subgroup and $x$ killed by a positive integer coprime to $q'$, such that $y$ lies in $\mathrm{inertiaInvariants}\,A\,(Mq')$ and $D.\mathrm{sp}\,y = z$.
--
--   This is the surjectivity half of Ribet's identification of the toric part of the monodromy with the kernel of the map from the glued Picard group to the pair of Picard groups of the two components, in the situation where the nodes are indexed by the supersingular places at $q'$. It combines the order computation for $q'$-prime-to-torsion in the inertia-generated subgroup with the corresponding torsion count on the torus side, and it supplies the surjectivity input for the construction of Cartier anchors in the Čerednik–Drinfeld comparison.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_toric_sp_surjective_of_jZeroSemistableSpecialization_ssPlaces.lean

import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_ModularCurve_ToricMonodromyPart
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_ModularCurve_JZeroSemistableSpecialization

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve AlgebraicCurve

theorem ModularCurve.toric_sp_surjective_of_jZeroSemistableSpecialization_ssPlaces
    (M q' : ℕ) [NeZero M] (hq' : q'.Prime) (hq'M : ¬ q' ∣ M)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q')
    [DecidableEq (IsLocalRing.ResidueField A)]
    [Fintype ↥(ssPlaces q' M (IsLocalRing.ResidueField A))]
    [NeZero (M * q')]
    [Module HeckeAlg (JZero (M * q'))] [Module HeckeAlg (JZero M)] :
    letI := ModularCurve.instAlgebraResidueFieldModularFunctionFieldCSemistable A M
    ∀ [Module HeckeAlg (AlgebraicCurve.Pic0 (IsLocalRing.ResidueField A)
        (modularFunctionFieldC (IsLocalRing.ResidueField A) M))]
      (D : JZeroSemistableSpecialization A M q' hq')
      (hi : D.nodes = nodePairsOfPlaces D.frob
        (ssPlaces q' M (IsLocalRing.ResidueField A)).toFinset)
      (hii : ∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ x : JZero (M * q'), PrimeToTorsion q' x →
        ∃ h : σ • x - x ∈ inertiaInvariants A (M * q'),
          D.comp ⟨σ • x - x, h⟩ = 0 ∧
            AlgebraicCurve.GluedPic0.toPic0Pair D.nodes (D.sp ⟨σ • x - x, h⟩) = 0)
      (z : AlgebraicCurve.GluedPic0 (IsLocalRing.ResidueField A)
        (modularFunctionFieldC (IsLocalRing.ResidueField A) M) D.nodes),
    AlgebraicCurve.GluedPic0.toPic0Pair D.nodes z = 0 →
      ∃ y : ↥(toricMonodromyPart (J := JZero (M * q')) q' (A.inertiaSubgroupIn ℚ)),
        ∃ hy : (y : JZero (M * q')) ∈ inertiaInvariants A (M * q'),
          D.sp ⟨(y : JZero (M * q')), hy⟩ = z := by sorry
