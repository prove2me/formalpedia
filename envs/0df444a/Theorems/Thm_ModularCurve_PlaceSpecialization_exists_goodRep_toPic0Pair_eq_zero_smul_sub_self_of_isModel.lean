-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_exists_goodRep_toPic0Pair_eq_zero_smul_sub_self_of_isModel
-- name    : ModularCurve.PlaceSpecialization.exists_goodRep_toPic0Pair_eq_zero_smul_sub_self_of_isModel
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.056571+00:00
-- url     : https://prove2.me/theorems/dec640a0-51bc-5b11-b0e9-230e487ff775
-- title:
--   Inertia displacement of prime-to-q torsion: good divisor with vanishing Pic⁰ pair
-- statement:
--   Let $N$ be a nonzero natural number and $q$ a prime not dividing $N$, and let $A$ be a valuation subring of a fixed algebraic closure $\overline{\mathbb{Q}}$ of $\mathbb{Q}$ lying over $q$, in the sense that the image of $q$ is a nonunit of $A$; consequently the residue field $k = \mathrm{ResidueField}\,A$ has characteristic $q$. Fix a finite set $W$ of places of the level-$N$ modular function field $\mathrm{modularFunctionFieldC}\,k\,N$ whose members are exactly the supersingular places (rational, affine geometric, with $j$-value in the supersingular set for $q$), a modular polynomial datum $\mathrm{data}$ for $q$ satisfying the Kronecker congruence $\Phi \equiv (Y^q - X)(Y - X^q) \bmod q$, hypotheses $h\alpha$, $h\beta$ asserting integrality of the two degeneracy maps $\bar\alpha$, $\bar\beta$ from level $N$ to level $Nq$ over $\overline{\mathbb{Q}}$, a place-specialization datum $P$ for $(A,q,N,\mathrm{data})$ with target $k$ and reduction the residue map of $A$, and a prolongation tuple $R$ for $P$ satisfying `IsModel` (the two divisor laws together with the cusp laws at $\infty$ and at $0$), the regularity law and the node-value law for $W$, and the fixed-point order law. Then for every $\sigma$ in the inertia subgroup of $A$ over $\mathbb{Q}$, viewed inside $\overline{\mathbb{Q}} \simeq_{\mathbb{Q}} \overline{\mathbb{Q}}$, and every $x \in \mathrm{Pic}^0$ of the level-$Nq$ modular function field over $\overline{\mathbb{Q}}$ killed by some positive integer prime to $q$, there is a degree-zero divisor $D$ on that field such that: every place in the support of $D$ is strict for $P$ on one of the two sides (its first reduction maps under geometric Frobenius to its second reduction, or conversely, with the relevant reduction not fixed by the square of Frobenius); the gluing datum $P.\mathrm{glueData}$ of $D$ at the node pairs $\{(w, \mathrm{arithFrobC}\cdot w) : w \in W\}$ — namely the pair of pushforward divisors of the two strict parts of $D$ along the two reduction legs, with zero node-unit coordinate — is admissible, i.e. both divisors have degree zero and vanish at the corresponding coordinates of each node pair; $\mathrm{Pic}^0.\mathrm{mk}\,D = \sigma \cdot x - x$; and the class of this gluing datum in $\mathrm{GluedPic}^0$ has vanishing image under `GluedPic0.toPic0Pair`, so that both pushforward divisors are principal.
--
--   This is the divisor-level form of the statement that the inertial displacement $\sigma x - x$ of a prime-to-$q$ torsion class on the Jacobian of the level-$Nq$ modular curve is represented by a divisor whose reduction data on the two components of the semistable special fibre are principal, the whole class being concentrated in the node-unit coordinates of the glued Picard group. It is the input to the statements on good glued specializations, on vanishing of the component map on such displacements, and on inertia invariance of prime-to-$q$ torsion displacements, in the Ribet-style analysis of the $q$-adic monodromy of $J_0(Nq)$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_exists_goodRep_toPic0Pair_eq_zero_smul_sub_self_of_isModel.lean

import Definitions.Def_ModularCurve_GlueData
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_ModularCurve_CoeffSemilinearAut
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

theorem ModularCurve.PlaceSpecialization.exists_goodRep_toPic0Pair_eq_zero_smul_sub_self_of_isModel
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
      (P : PlaceSpecialization A q N data hKr (ResidueField A) (IsLocalRing.residue A) hα hβ) (R : ProlongationTuple P) (hR : R.IsModel) (hRL : R.RegularityLaw W) (hNV : R.NodeValueLaw W) (hO : R.OrderLawFixed),
        ∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ x : JZero (N * q),
          PrimeToTorsion q x →
            ∃ (D : ↥(Divisor.degZero (K := AlgebraicClosure ℚ)
                (F := ↥(modularFunctionFieldBar (N * q)))))
              (_ : P.IsGoodDiv (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))))
              (hadm : P.glueData (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W)
                  (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))
                ∈ GluingData.admissible
                    (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W)),
              Pic0.mk D = σ • x - x ∧
                GluedPic0.toPic0Pair (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W)
                  (GluedPic0.mk (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W)
                    ⟨P.glueData (nodePairsOfPlaces (arithFrobC q (ResidueField A) N) W)
                      (D : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))), hadm⟩)
                  = 0 := by sorry
