-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_smul_sub_self_mem_inertiaInvariants_of_primeToTorsion_of_isModel_levelOne
-- name    : ModularCurve.PlaceSpecialization.smul_sub_self_mem_inertiaInvariants_of_primeToTorsion_of_isModel_levelOne
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.056571+00:00
-- url     : https://prove2.me/theorems/ecc04262-9e96-5ceb-9ee6-553198de41b6
-- title:
--   Inertia acts unipotently on prime-to-q torsion of J₀(q)
-- statement:
--   Let $q$ be a prime and let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ lying over $q$, in the sense that $q$ is a non-unit of $A$; consequently the residue field $k_A = \mathrm{ResidueField}\,A$ has characteristic $q$, and it is algebraically closed. Fix: a finite set $W$ of places of $\mathrm{modularFunctionFieldC}\,k_A\,1$ over $k_A$ whose members are exactly the supersingular places for $q$ (the places that are rational, affine geometric — both the $j$- and $j_N$-generators lie in the valuation subring — and whose value at the $j$-generator lies in $\mathrm{ssJSet}\,q$); modular polynomial data `data` for $q$ (a monic $\Phi \in \mathbb{Z}[X][Y]$ of degree $\psi(q)$ annihilating the pair $(j, j_q)$ of $q$-expansions) satisfying the Kronecker congruence $\Phi \equiv (C(X)^q - X)(C(X) - X^q) \bmod q$; integrality of the two degeneracy embeddings $\mathrm{heckeAlphaBar}$ and $\mathrm{heckeBetaBar}$ from level $1$ to level $1\cdot q$ over $\overline{\mathbb{Q}}$; a place specialisation $P$ for $A$, $q$, level $1$, these data, target field $k_A$ and reduction $\mathrm{residue}\,A$; and a prolongation tuple $R$ for $P$ which is a model (the two divisor laws and the two cusp laws at $\infty$ and $0$) and satisfies $\mathrm{RegularityLaw}\,W$, $\mathrm{NodeValueLaw}\,W$ and $\mathrm{OrderLawFixed}$. Then for every $\sigma$ in the inertia subgroup of $A$ inside $\overline{\mathbb{Q}} \simeq_{\mathbb{Q}} \overline{\mathbb{Q}}$ and every $x$ in $\mathrm{JZero}\,(1\cdot q)$, the degree-zero divisor class group of the level-$q$ modular function field over $\overline{\mathbb{Q}}$, which is prime-to-$q$ torsion (killed by some $n > 0$ with $q \nmid n$), the difference $\sigma \bullet x - x$ is fixed by every element of that inertia subgroup.
--
--   This is the unipotency statement underlying Mazur's principle: inertia at $q$ acts on the prime-to-$q$ torsion of the Jacobian of $X_0(q)$ through a group in which $(\sigma - 1)(\tau - 1)$ annihilates, so that $(\sigma-1)x$ is inertia-invariant. It is the level-one case ($N = 1$) of the corresponding statement at level $Nq$, and feeds the arithmetic Galois step [`ModularCurve.arithmeticGalois_smul_sub_mem_inertiaInvariantPoints`](thm.html#ModularCurve.arithmeticGalois_smul_sub_mem_inertiaInvariantPoints).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_smul_sub_self_mem_inertiaInvariants_of_primeToTorsion_of_isModel_levelOne.lean

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
set_option autoImplicit false

theorem ModularCurve.PlaceSpecialization.smul_sub_self_mem_inertiaInvariants_of_primeToTorsion_of_isModel_levelOne
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
        ∀ (R : ProlongationTuple P) (hR : R.IsModel) (hRL : R.RegularityLaw W)
          (hNV : R.NodeValueLaw W) (hO : R.OrderLawFixed),
          ∀ σ ∈ A.inertiaSubgroupIn ℚ, ∀ x : JZero (1 * q),
            PrimeToTorsion q x → σ • x - x ∈ inertiaInvariants A (1 * q) := by sorry
