-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_exists_goodRep_toPic0Pair_eq_zero_smul_sub_self_levelOne
-- name    : ModularCurve.PlaceSpecialization.exists_goodRep_toPic0Pair_eq_zero_smul_sub_self_levelOne
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.056571+00:00
-- url     : https://prove2.me/theorems/b3ac5adb-6976-59a0-997e-ad1ad83219e2
-- title:
--   Good admissible representatives of inertia displacements at level q
-- statement:
--   Let $q$ be a prime and let $A$ be a valuation subring of $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ` with `A.LiesOverPrime q`, i.e. $q$ is a non-unit of $A$; consequently the residue field $k =$ `ResidueField A` has characteristic $q$. Let $W$ be a finite set of places of `modularFunctionFieldC k 1` over $k$ whose members are exactly the supersingular places `ssPlaces q 1 k` (those places that are rational, affine geometric, and whose value of the geometric $j$-invariant lies in `ssJSet q k`); let `data : ModularPolynomialData q` be a monic bivariate modular polynomial $\Phi$ of degree `dedekindPsi q` annihilating the pair $(j, j_q)$, satisfying the Kronecker congruence $\Phi \equiv (C X^q - X)(C X - X^q) \bmod q$; let `hα`, `hβ` assert that the two degeneracy embeddings `heckeAlphaBar` and `heckeBetaBar` from level $1$ to level $1\cdot q$ over $\overline{\mathbb{Q}}$ are integral ring homomorphisms; and let $P$ be a `PlaceSpecialization` for $A$, $q$, level $1$, `data`, `hKr`, the residue field $k$ and the residue map $A \to k$, with these integrality data. Write $S =$ `nodePairsOfPlaces (arithFrobC q k 1) W` for the finite set of node pairs obtained by pairing each $w \in W$ with its image under the semilinear arithmetic Frobenius. Then for every $\sigma$ in the inertia subgroup of $A$ over $\mathbb{Q}$ (the image in $\overline{\mathbb{Q}} \simeq_{\mathbb{Q}} \overline{\mathbb{Q}}$ of the inertia subgroup inside the decomposition subgroup) and every $x \in$ `JZero (1 * q)` $= \mathrm{Pic}^0$ of `modularFunctionFieldBar (1 * q)` over $\overline{\mathbb{Q}}$ with `PrimeToTorsion q x` (some $n > 0$ with $q \nmid n$ and $n \cdot x = 0$), there is a degree-zero divisor $D$ on the level-$(1\cdot q)$ curve over $\overline{\mathbb{Q}}$ such that: every place in the support of $D$ satisfies `P.IsStrictFst` or `P.IsStrictSnd`; the gluing datum `P.glueData S D`, namely the pair of pushforwards of the strict-first and strict-second parts of $D$ along `P.reduceFst` and `P.reduceSnd` together with the trivial unit component, is admissible for $S$ (both divisors of degree zero and vanishing at the respective coordinates of each pair in $S$); the divisor class of $D$ equals $\sigma \cdot x - x$; and the image of the glued class of that admissible datum under `GluedPic0.toPic0Pair` is zero, i.e. both pushed-forward divisors are principal.
--
--   This is the level-one case ($N = 1$, so level $1 \cdot q$) of the statement that an inertial displacement $\sigma x - x$ of a prime-to-$q$ torsion class on the Jacobian of the level-$q$ modular curve is represented by a divisor whose specialisation to the two components of the semistable reduction at $q$ is principal on each component, the remaining information being concentrated in the node units. It feeds the computation of inertia invariants in [`ModularCurve.PlaceSpecialization.smul_sub_self_mem_inertiaInvariants_of_primeToTorsion_of_isModel_levelOne`](thm.html#ModularCurve.PlaceSpecialization.smul_sub_self_mem_inertiaInvariants_of_primeToTorsion_of_isModel_levelOne).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_exists_goodRep_toPic0Pair_eq_zero_smul_sub_self_levelOne.lean

import Definitions.Def_ModularCurve_GlueData
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_ModularCurve_CoeffSemilinearAut
import Definitions.Def_ValuationSubring_ReduceAt
import Definitions.Def_WeierstrassCurve_ReductionMap

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
set_option Elab.async false
open AlgebraicCurve IsLocalRing ModularCurve
set_option autoImplicit false

theorem ModularCurve.PlaceSpecialization.exists_goodRep_toPic0Pair_eq_zero_smul_sub_self_levelOne
    (q : ℕ) (hq : q.Prime)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q) :
    haveI : NeZero q := ⟨hq.ne_zero⟩
    haveI : Fact q.Prime := ⟨hq⟩
    haveI : CharP (ResidueField A) q := ValuationSubring.charP_residueField_of_liesOverPrime_def hq hA
    letI := instDecidableEqResidueFieldSemistable A
    letI := instAlgebraResidueFieldModularFunctionFieldCSemistable A 1
    ∀ (W : Finset (Place (ResidueField A) (modularFunctionFieldC (ResidueField A) 1)))
      (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q 1 (ResidueField A))
      (data : ModularPolynomialData q) (hKr : KroneckerCongruence q data)
      (hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q)
      (hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q)
      (P : PlaceSpecialization A q 1 data hKr (ResidueField A) (IsLocalRing.residue A) hα hβ),
        ∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ x : JZero (1 * q),
          PrimeToTorsion q x →
            ∃ (D : ↥(Divisor.degZero (K := AlgebraicClosure ℚ)
                (F := ↥(modularFunctionFieldBar (1 * q)))))
              (_ : P.IsGoodDiv (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))))
              (hadm : P.glueData (nodePairsOfPlaces (arithFrobC q (ResidueField A) 1) W)
                  (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)))
                ∈ GluingData.admissible
                    (nodePairsOfPlaces (arithFrobC q (ResidueField A) 1) W)),
              Pic0.mk D = σ • x - x ∧
                GluedPic0.toPic0Pair (nodePairsOfPlaces (arithFrobC q (ResidueField A) 1) W)
                  (GluedPic0.mk (nodePairsOfPlaces (arithFrobC q (ResidueField A) 1) W)
                    ⟨P.glueData (nodePairsOfPlaces (arithFrobC q (ResidueField A) 1) W)
                      (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))), hadm⟩)
                  = 0 := by sorry
