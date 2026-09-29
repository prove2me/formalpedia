-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_exists_goodRep_admissible_smul_single_sub_self_of_isModel
-- name    : ModularCurve.PlaceSpecialization.exists_goodRep_admissible_smul_single_sub_self_of_isModel
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.056571+00:00
-- url     : https://prove2.me/theorems/02e70b26-e144-5a60-b21c-04dabf1e9584
-- title:
--   Inertia displacements σ V-V admit good admissible representatives
-- statement:
--   Fix $N$ with $N \neq 0$ and a prime $q$ with $q \nmid N$, and a valuation subring $A$ of $\overline{\mathbb Q}$ lying over $q$ in the sense that $q$ is a non-unit of $A$; then the residue field $k = \mathrm{ResidueField}\,A$ has characteristic $q$. Let $W$ be a finite set of places of $\mathrm{modularFunctionFieldC}\,k\,N$ whose members are exactly the supersingular places (rational, affine geometric, with $j$-value in the supersingular set), let `data` be modular polynomial data for $q$ satisfying the Kronecker congruence $\Phi \equiv (X'^q - X)(X' - X^q) \bmod q$, let $h\alpha$, $h\beta$ assert integrality of the two degeneracy maps $\mathrm{modularFunctionFieldBar}\,N \to \mathrm{modularFunctionFieldBar}\,(Nq)$, let $P$ be a `PlaceSpecialization` from level $Nq$ over $\overline{\mathbb Q}$ to level $N$ over $k$ along the residue map of $A$, and let $R$ be a prolongation tuple over $P$ satisfying `IsModel` (both divisor laws and both cusp laws), the regularity law for $W$, and the order law at Frobenius-fixed affine places. Then for every $\sigma$ in the inertia subgroup of $A$ inside $\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$ and every place $V$ of $\mathrm{modularFunctionFieldBar}\,(Nq)$ which is neither strict on the first side nor strict on the second side and whose first reduction $P.\mathrm{reduceFst}\,V$ lies in $W$, given that the divisor $\sigma\!\cdot\!V - V$ has degree zero, there is a degree-zero divisor $D$ on $\mathrm{modularFunctionFieldBar}\,(Nq)$ that is good (every place in its support is strict on the first or on the second side) and whose gluing datum at the node pairs of $W$ formed by the arithmetic Frobenius semilinear automorphism is admissible (the two pushed-forward divisors $\mathrm{reduceFst}_*$ of the strict-first part and $\mathrm{reduceSnd}_*$ of the strict-second part have degree zero and vanish at the respective coordinates of each node pair), such that $D$ and $\sigma\!\cdot\!V - V$ have the same class in $\mathrm{Pic}^0$.
--
--   This is the divisor-class form of the statement that an inertia displacement on the geometric fibre lands in the identity component of the special fibre of the Néron model of the Jacobian of $X_0(Nq)$: the class is represented by a divisor meeting only the smooth locus of the semistable model and having componentwise degree zero. It feeds the construction of the Néron-model dictionary, being cited by [`ModularCurve.DRModelPackageLevel.extendsToPlace_pts_smul_sub`](thm.html#ModularCurve.DRModelPackageLevel.extendsToPlace_pts_smul_sub) and by [`ModularCurve.PlaceSpecialization.exists_goodRep_toPic0Pair_eq_zero_smul_sub_self_of_isModel`](thm.html#ModularCurve.PlaceSpecialization.exists_goodRep_toPic0Pair_eq_zero_smul_sub_self_of_isModel).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_exists_goodRep_admissible_smul_single_sub_self_of_isModel.lean

import Definitions.Def_ModularCurve_GlueData
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_ModularCurve_CoeffSemilinearAut
import Definitions.Def_ValuationSubring_ReduceAt
import Definitions.Def_WeierstrassCurve_ReductionMap
import Definitions.Def_ModularCurve_ProlongationTuple

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve IsLocalRing ModularCurve

theorem ModularCurve.PlaceSpecialization.exists_goodRep_admissible_smul_single_sub_self_of_isModel
    (N q : ℕ) [NeZero N] (hq : q.Prime) (hqN : ¬ q ∣ N)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q) :
    haveI : NeZero q := ⟨hq.ne_zero⟩
    haveI : Fact q.Prime := ⟨hq⟩
    haveI : CharP (ResidueField A) q := ValuationSubring.charP_residueField_of_liesOverPrime_def hq hA
    letI := instDecidableEqResidueFieldSemistable A
    letI := instAlgebraResidueFieldModularFunctionFieldCSemistable A N
    ∀ (W : Finset (Place (ResidueField A) (modularFunctionFieldC (ResidueField A) N)))
      (hW : ∀ w, w ∈ W ↔ w ∈ ssPlaces q N (ResidueField A))
      (data : ModularPolynomialData q) (hKr : KroneckerCongruence q data)
      (hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q)
      (hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q)
      (P : PlaceSpecialization A q N data hKr (ResidueField A) (IsLocalRing.residue A) hα hβ)
      (R : ProlongationTuple P) (hR : R.IsModel) (hRL : R.RegularityLaw W) (hO : R.OrderLawFixed),
        ∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ (V : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))),
          ¬ P.IsStrictFst V → ¬ P.IsStrictSnd V → P.reduceFst V ∈ W →
          ∀ (hdeg : arithmeticGalois (modularFunctionFieldFull (N * q)) σ • (Finsupp.single V (1 : ℤ))
              - Finsupp.single V 1
              ∈ Divisor.degZero (K := AlgebraicClosure ℚ) (F := ↥(modularFunctionFieldBar (N * q)))),
            ∃ (D : ↥(Divisor.degZero (K := AlgebraicClosure ℚ)
                (F := ↥(modularFunctionFieldBar (N * q)))))
              (_ : P.IsGoodDiv (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))))
              (hadm : P.glueData (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W)
                  (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))
                ∈ GluingData.admissible
                    (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W)),
              Pic0.mk D = Pic0.mk ⟨arithmeticGalois (modularFunctionFieldFull (N * q)) σ • (Finsupp.single V (1 : ℤ))
                - Finsupp.single V 1, hdeg⟩ := by sorry
