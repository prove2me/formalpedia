-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_IsGluedSpecialization_isGoodClass_and_toPic0Pair_apply_smul_sub_self_of_isModel
-- name    : ModularCurve.PlaceSpecialization.IsGluedSpecialization.isGoodClass_and_toPic0Pair_apply_smul_sub_self_of_isModel
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.572352+00:00
-- url     : https://prove2.me/theorems/dd97c102-0cee-5ba4-99c8-6f41822906b4
-- title:
--   Inertial displacements of prime-to-q torsion are good toric classes
-- statement:
--   Fix $N\ge 1$ and a prime $q$ with $q\nmid N$, and let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ with $q$ a non-unit of $A$, so that the residue field $\kappa=\mathrm{ResidueField}\,A$ has characteristic $q$. Let $W$ be a finite set of places of the level-$N$ modular function field $\mathrm{modularFunctionFieldC}\,\kappa\,N$ consisting exactly of the supersingular places, i.e. $w\in W$ if and only if $w\in \mathrm{ssPlaces}\,q\,N\,\kappa$, and let $S=\mathrm{nodePairsOfPlaces}(\mathrm{arithFrobC}\,q\,\kappa\,N)\,W$ be the image of $W$ under $w\mapsto (w,\ \mathrm{arithFrobC}\cdot w)$; it is assumed node-stable under the arithmetic Frobenius semilinear automorphism. Let `data` be a modular polynomial datum for $q$ satisfying the Kronecker congruence $\Phi\equiv (C(X)^q-X)(C(X)-X^q)$ modulo $q$, let the two degeneracy embeddings $\mathrm{heckeAlphaBar}$, $\mathrm{heckeBetaBar}$ for $(N,q)$ over $\overline{\mathbb{Q}}$ be integral, let $P$ be a place-specialization datum for $(A,q,N,\mathrm{data})$ with residue map $\mathrm{residue}\,A$, and let $R$ be a prolongation tuple for $P$ satisfying `IsModel` (the two divisor laws and the two cusp laws), the regularity law and the node value law for $W$, and the fixed-point order law. Finally let $\mathrm{sp}$ be an additive homomorphism from the subgroup of classes in $\mathrm{JZero}(Nq)=\mathrm{Pic}^0$ of the level-$Nq$ modular function field over $\overline{\mathbb{Q}}$ fixed by the inertia subgroup $\mathrm{inertiaSubgroupIn}\,\mathbb{Q}\,A$ to the glued group $\mathrm{GluedPic0}\,\kappa\,(\mathrm{modularFunctionFieldC}\,\kappa\,N)\,S$, which is a glued specialization for $P$: for every degree-zero divisor $D$ whose class is inertia-invariant, every admissible gluing datum equal to $P.\mathrm{glueData}\,S\,D$ and every good $D$ (each place of the support being strict-first or strict-second for $P$), $\mathrm{sp}$ sends the class of $D$ to the class of that gluing datum. The conclusion: for every $\sigma$ in the inertia subgroup and every $x\in\mathrm{JZero}(Nq)$ killed by some $n>0$ with $q\nmid n$, the element $\sigma\cdot x-x$ is inertia-invariant, it is a good class for $P$ relative to $S$ (represented by a degree-zero good divisor whose glue datum is admissible), and the image of $\mathrm{sp}(\sigma\cdot x-x)$ under $\mathrm{GluedPic0.toPic0Pair}$, the projection to the pair of $\mathrm{Pic}^0$ groups of the two components, is zero.
--
--   This is the toric-specialization statement for the monodromy of the semistable reduction of $X_0(Nq)$ at $q$: inertial displacements $\sigma x-x$ on prime-to-$q$ torsion specialize into the kernel of the projection of the glued degree-zero class group onto the product of the class groups of the two components. It feeds the identification of these displacements with toric points and with node units in the level-lowering argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_IsGluedSpecialization_isGoodClass_and_toPic0Pair_apply_smul_sub_self_of_isModel.lean

import Definitions.Def_ModularCurve_GlueData
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_ModularCurve_CoeffSemilinearAut
import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_ValuationSubring_ReduceAt
import Definitions.Def_WeierstrassCurve_ReductionMap
import Definitions.Def_ModularCurve_ProlongationTuple

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option Elab.async false
open AlgebraicCurve IsLocalRing ModularCurve

theorem ModularCurve.PlaceSpecialization.IsGluedSpecialization.isGoodClass_and_toPic0Pair_apply_smul_sub_self_of_isModel (N q : ℕ) [NeZero N] (hq : q.Prime) (hqN : ¬ q ∣ N)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q) :
    haveI : NeZero q := ⟨hq.ne_zero⟩
    haveI : Fact q.Prime := ⟨hq⟩
    haveI : CharP (ResidueField A) q := ValuationSubring.charP_residueField_of_liesOverPrime_def hq hA
    letI := heckeModuleBar (N * q)
    letI := heckeModuleBar N
    letI := instDecidableEqResidueFieldSemistable A
    letI := instAlgebraResidueFieldModularFunctionFieldCSemistable A N
    ∀ (W : Finset (Place (ResidueField A) (modularFunctionFieldC (ResidueField A) N)))
      (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q N (ResidueField A))
      (hstab : SemilinearAut.IsNodeStable
        (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W) (arithFrobC q (ResidueField A) N))
      (data : ModularPolynomialData q) (hKr : KroneckerCongruence q data)
      (hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q)
      (hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q)
      (P : PlaceSpecialization A q N data hKr (ResidueField A) (IsLocalRing.residue A) hα hβ) (R : ProlongationTuple P) (hR : R.IsModel) (hRL : R.RegularityLaw W) (hNV : R.NodeValueLaw W) (hO : R.OrderLawFixed)
      (sp : ↥(inertiaInvariants A (N * q)) →+
        GluedPic0 (ResidueField A) (modularFunctionFieldC (ResidueField A) N)
          (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W))
      (hsp : P.IsGluedSpecialization (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W) sp),
        (∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ x : JZero (N * q),
          PrimeToTorsion q x →
            ∃ h : σ • x - x ∈ inertiaInvariants A (N * q),
              P.IsGoodClass
                (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W) (σ • x - x) ∧
                GluedPic0.toPic0Pair (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W)
                  (sp ⟨σ • x - x, h⟩) = 0) := by sorry
