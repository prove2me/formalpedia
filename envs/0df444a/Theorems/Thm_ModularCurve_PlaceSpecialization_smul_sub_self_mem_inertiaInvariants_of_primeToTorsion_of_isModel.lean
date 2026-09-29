-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_smul_sub_self_mem_inertiaInvariants_of_primeToTorsion_of_isModel
-- name    : ModularCurve.PlaceSpecialization.smul_sub_self_mem_inertiaInvariants_of_primeToTorsion_of_isModel
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.056571+00:00
-- url     : https://prove2.me/theorems/ef145704-e164-5cfa-bf81-d8df0bbb3e94
-- title:
--   Inertia-invariance of inertial displacements of prime-to-q torsion
-- statement:
--   Fix a natural number $N \neq 0$ and a prime $q$ with $q \nmid N$, and let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ lying over $q$ in the sense that $q$ belongs to the nonunits of $A$; consequently the residue field $\kappa = \operatorname{ResidueField} A$ has characteristic $q$. The assertion is then: for every finite set $W$ of places of the function field $\mathtt{modularFunctionFieldC}\ \kappa\ N$ over $\kappa$ whose members are exactly the supersingular places $\mathtt{ssPlaces}\ q\ N\ \kappa$ (those rational places at which both $j$-generators are integral and whose $j$-value lies in the supersingular set for $q$), for every modular polynomial datum `data` for $q$ (a monic $\Phi \in \mathbb{Z}[X][Y]$ of degree $\psi(q)$ annihilating the pair of $q$-expansions of $j$) satisfying the Kronecker congruence $\Phi \equiv (X^q - Y)(X - Y^q) \bmod q$, given integrality of the two level-raising maps $\mathtt{heckeAlphaBar}$ and $\mathtt{heckeBetaBar}$ from level $N$ to level $Nq$ over $\overline{\mathbb{Q}}$, a place specialisation $P$ of the level-$N$ data at $A$ with target $\kappa$ and reduction map the residue map of $A$, and a prolongation tuple $R$ for $P$ satisfying `IsModel` (the two divisor laws and the two cusp laws), the regularity law for $W$, the node-value law for $W$ and the order law at Frobenius-fixed affine places: for every $\sigma$ in the inertia subgroup of $A$ over $\mathbb{Q}$ and every class $x$ in $\mathtt{JZero}\,(Nq)$, the degree-zero divisor class group of the level-$Nq$ modular function field over $\overline{\mathbb{Q}}$, if $n \cdot x = 0$ for some $n > 0$ with $q \nmid n$, then $\sigma \cdot x - x$ is fixed by every element of that inertia subgroup.
--
--   This is the invariance half of Mazur's principle as it enters Ribet's level-lowering argument: inertia at a place above $q$ acts trivially on the prime-to-$q$ torsion of $J_0(Nq)$, expressed here in terms of a semistable model datum at $A$. It is used by the statements which, for a glued specialisation, identify the good class and the vanishing of its image in the pair of Picard groups, and which deduce that the inertial displacement itself vanishes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_smul_sub_self_mem_inertiaInvariants_of_primeToTorsion_of_isModel.lean

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

theorem ModularCurve.PlaceSpecialization.smul_sub_self_mem_inertiaInvariants_of_primeToTorsion_of_isModel
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
      (P : PlaceSpecialization A q N data hKr (ResidueField A) (IsLocalRing.residue A) hα hβ),
        ∀ (R : ProlongationTuple P) (hR : R.IsModel) (hRL : R.RegularityLaw W)
          (hNV : R.NodeValueLaw W) (hO : R.OrderLawFixed),
          ∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ x : JZero (N * q),
            PrimeToTorsion q x → σ • x - x ∈ inertiaInvariants A (N * q) := by sorry
