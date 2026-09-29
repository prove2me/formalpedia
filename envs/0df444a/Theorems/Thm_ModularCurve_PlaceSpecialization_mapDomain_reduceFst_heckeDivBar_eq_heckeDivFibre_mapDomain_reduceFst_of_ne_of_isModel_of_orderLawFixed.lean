-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_mapDomain_reduceFst_heckeDivBar_eq_heckeDivFibre_mapDomain_reduceFst_of_ne_of_isModel_of_orderLawFixed
-- name    : ModularCurve.PlaceSpecialization.mapDomain_reduceFst_heckeDivBar_eq_heckeDivFibre_mapDomain_reduceFst_of_ne_of_isModel_of_orderLawFixed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.056571+00:00
-- url     : https://prove2.me/theorems/dd0b622c-26ed-578f-a303-d98186718d77
-- title:
--   First reduction intertwines T_ℓ with the fibre correspondence
-- statement:
--   Fix $N\ge 1$ and a prime $q$, and let $A$ be a valuation subring of $\overline{\mathbb Q}$ lying over $q$ in the sense that $q$ is a non-unit of $A$; its residue field $\kappa = \mathrm{ResidueField}\,A$ then has characteristic $q$. Let `data` be modular polynomial data for $q$ (a monic $\Phi\in\mathbb Z[X][Y]$ of degree $\psi(q)$ annihilating the pair $(j, j_q)$ of $q$-expansions) satisfying the Kronecker congruence $\Phi \equiv (Y^{q}-X)(Y-X^{q}) \pmod q$, let $h\alpha,h\beta$ be the integrality hypotheses for the two degeneracy embeddings of the level-$N$ function field into the level-$Nq$ function field over $\overline{\mathbb Q}$, and let $P$ be a place specialisation of level $N$ at $A$ with reduction map the residue map $A\to\kappa$. Let $\ell$ be a prime with $\ell\neq q$, let $h\alpha_\ell,h\beta_\ell$ be integrality of the degeneracy embeddings from level $Nq$ into level $Nq\ell$ over $\overline{\mathbb Q}$, assume principal divisors of degree zero exist on the level-$Nq\ell$ field over $\overline{\mathbb Q}$, assume $q\nmid N$, and let $R$ be a prolongation tuple for $P$ satisfying `IsModel` (the two divisor laws at the places not fixed by the square of the geometric Frobenius together with the two cusp laws) and `OrderLawFixed` (at affine geometric places fixed by that square, the pushforward of a principal divisor along `reduceFst` is the sum of the orders of the two residues). Assume further that principal divisors of degree zero exist on the characteristic-$q$ degeneracy roof $\mathrm{charLDegeneracyRoof}\,\kappa\,N\,\ell$, generated over $\kappa$ by $j$, $j_N$, $j_\ell$ and $j_{N\ell}$, and that the two embeddings $\beta_C,\alpha_C$ of the level-$N$ function field over $\kappa$ into that roof are integral. Then for every divisor $X$ on the level-$Nq$ function field over $\overline{\mathbb Q}$, the pushforward along `P.reduceFst` (restriction along the first degeneracy embedding of level $N$ into level $Nq$, followed by $P.\mathrm{sp}$) of the correspondence $\mathrm{heckeDivBar}$ at level $Nq$ and prime $\ell$ (pullback along $\beta$ then pushforward along $\alpha$) coincides with the fibre correspondence $\mathrm{heckeDivFibre}$ at level $N$ over $\kappa$ (pullback along $\beta_C$ then pushforward along $\alpha_C$) applied to the pushforward of $X$ along `P.reduceFst`.
--
--   This is the divisor-level statement that reduction of the level-$Nq$ curve onto the level-$N$ special fibre via the first degeneracy map commutes with the Hecke correspondence $T_\ell$ for $\ell\neq q$, with the auxiliary prolongation data produced from the given prolongation tuple rather than assumed. It feeds the computations of the action of Hecke operators on the component group of the special fibre at $q$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_mapDomain_reduceFst_heckeDivBar_eq_heckeDivFibre_mapDomain_reduceFst_of_ne_of_isModel_of_orderLawFixed.lean

import Definitions.Def_ValuationSubring_ReduceAt
import Definitions.Def_ModularCurve_SupersingularNodePlaces
import Definitions.Def_ModularCurve_CoeffSemilinearAut
import Definitions.Def_ModularCurve_GlueData
import Definitions.Def_ModularCurve_ProlongationTuple
import Definitions.Def_ModularCurve_CharLDegeneracyHecke

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000
open IsLocalRing
open AlgebraicCurve

theorem ModularCurve.PlaceSpecialization.mapDomain_reduceFst_heckeDivBar_eq_heckeDivFibre_mapDomain_reduceFst_of_ne_of_isModel_of_orderLawFixed
    (N q : ℕ) [NeZero N] (hq : q.Prime)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q) :
    haveI : NeZero q := ⟨hq.ne_zero⟩
    haveI : Fact q.Prime := ⟨hq⟩
    haveI : CharP (ResidueField A) q := ValuationSubring.charP_residueField_of_liesOverPrime_def hq hA
    letI := instDecidableEqResidueFieldSemistable A
    letI := instAlgebraResidueFieldModularFunctionFieldCSemistable A N
    ∀ (data : ModularPolynomialData q) (hKr : KroneckerCongruence q data)
      (hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q)
      (hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q)
      (P : PlaceSpecialization A q N data hKr (ResidueField A) (IsLocalRing.residue A) hα hβ),
        ∀ ℓ : Nat.Primes, (ℓ : ℕ) ≠ q →
          haveI : NeZero (ℓ : ℕ) := ⟨ℓ.2.ne_zero⟩
          ∀ (hαℓ : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) (N * q) ℓ)
            (hβℓ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) (N * q) ℓ)
            [HasPrincipalDivisors (AlgebraicClosure ℚ) (modularFunctionFieldBar ((N * q) * ℓ))]
            (hqN : ¬ q ∣ N) (R : PlaceSpecialization.ProlongationTuple P) (hmodel : R.IsModel) (hO : R.OrderLawFixed)
            [HasPrincipalDivisors (ResidueField A) (charLDegeneracyRoof (ResidueField A) N ℓ)]
            (hβc : HeckeBetaCIntegral (ResidueField A) N ℓ) (hαc : HeckeAlphaCIntegral (ResidueField A) N ℓ),
            ∀ X : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)),
              Finsupp.mapDomain P.reduceFst (heckeDivBar hαℓ hβℓ X) =
                heckeDivFibre (ResidueField A) N ℓ hβc hαc (Finsupp.mapDomain P.reduceFst X) := by sorry
