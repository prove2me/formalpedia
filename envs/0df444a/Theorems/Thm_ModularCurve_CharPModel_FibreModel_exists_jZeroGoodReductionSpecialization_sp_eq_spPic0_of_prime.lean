-- Prove2me | Theorems.Thm_ModularCurve_CharPModel_FibreModel_exists_jZeroGoodReductionSpecialization_sp_eq_spPic0_of_prime
-- name    : ModularCurve.CharPModel.FibreModel.exists_jZeroGoodReductionSpecialization_sp_eq_spPic0_of_prime
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:12.70306+00:00
-- url     : https://prove2.me/theorems/ca3d711b-40ff-5ccf-a39f-69df976738c9
-- title:
--   Good-reduction specialisation datum for J₀(N), N prime
-- statement:
--   Fix a nonzero natural number $N$ that is prime, and assume `HeckeOperatorsCommuteBar N`, i.e. the operators `heckeOperatorBar N q` on $J_0(N) = \mathrm{Pic}^0$ of the geometric modular function field `modularFunctionFieldBar N` over $\overline{\mathbb{Q}}$ commute pairwise. Fix a prime $\ell$ with $\ell \nmid N$, a valuation subring $A$ of $\overline{\mathbb{Q}}$ with $\ell$ a non-unit of $A$, the residue field $\kappa_A$ of $A$ being of characteristic $\ell$, a fibre model `fm` of level $N$ over $A$ with reduction the residue map $A \to \kappa_A$, together with a cusp chart `cc` for it; modular polynomial data $\Phi_d$ for every divisor $d \mid N$, such that the reduction of $\Phi_N$ modulo the residue characteristic, read in $\kappa_A(X)[Y]$, is separable; the hypothesis that the divisor-level specialisation `fm.spDiv` carries degree-zero divisors to degree-zero divisors and principal degree-zero divisors to principal ones; that $N$ is squarefree and $\Phi_N$ satisfies `EvalSymm`; modular polynomial data for $\ell$ satisfying the Kronecker congruence $\Phi \equiv (Y^{\ell}-X)(Y-X^{\ell})$ modulo $\ell$; and an `IsCurveOver` structure on $\kappa_A \subseteq$ `modularFunctionFieldC κ_A N`. Then, with $J_0(N)$ carrying the Hecke-algebra structure `heckeModuleBar N`, there are a `HeckeAlg`-module structure on $\mathrm{Pic}^0(\kappa_A,$ `modularFunctionFieldC κ_A N`$)$ and a datum $D$ of type `JZeroGoodReductionSpecialization A ℓ hℓ.out N` — that is, a surjective additive map $\mathrm{sp}$ from $J_0(N)$ to that $\mathrm{Pic}^0$ which is Hecke-equivariant, invariant under the inertia subgroup of $A$ over $\mathbb{Q}$, intertwines any Frobenius element at $A$ over $\ell$ with an endomorphism $F$, is injective on $q$-power torsion for every prime $q \neq \ell$, and whose $F$ satisfies $F^2 - T_\ell F + \ell = 0$ — such that $D.\mathrm{sp}$ is exactly `fm.spPic0` for the given data and $D.F$ is the geometric Frobenius pushforward `frobeniusPushforwardGeomLevelPic0OfIsCurveOver` on $\mathrm{Pic}^0$ of the special fibre.
--
--   This packages the good reduction of $X_0(N)$ at a prime $\ell \nmid N$, together with the Eichler–Shimura relation on the special fibre, into the single datum used downstream, and pins its specialisation map to the explicitly constructed map on degree-zero divisor classes. It is the prime-level form of the statement and feeds [`ModularCurve.exists_jZeroGoodReductionSpecialization_doorPredicates`](thm.html#ModularCurve.exists_jZeroGoodReductionSpecialization_doorPredicates).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_CharPModel_FibreModel_exists_jZeroGoodReductionSpecialization_sp_eq_spPic0_of_prime.lean

import Definitions.Def_ModularCurve_SpecializationMap
import Definitions.Def_ModularCurve_FibreModelCuspChart
import Definitions.Def_ModularCurve_JZeroGoodReductionV2
import Definitions.Def_ModularCurve_StepThreeDoorPredicates
import Definitions.Def_ValuationSubring_ReduceAt

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve ModularCurve.CharPModel AlgebraicCurve IsLocalRing

attribute [local instance] ModularCurve.instDecEqResidueFieldF3nrp
  ModularCurve.instAlgebraResidueFieldModularFunctionFieldCF3nrp
set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem ModularCurve.CharPModel.FibreModel.exists_jZeroGoodReductionSpecialization_sp_eq_spPic0_of_prime
    (N : ℕ) [NeZero N] (hN : N.Prime) (hcomm : HeckeOperatorsCommuteBar N)
    (ℓ : ℕ) [hℓ : Fact ℓ.Prime] (hℓN : ¬ ℓ ∣ N)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime ℓ)
    [CharP (ResidueField ↥A) ℓ]
    (fm : FibreModel N A ℓ (ResidueField ↥A) (IsLocalRing.residue ↥A))
    (cc : fm.CuspChart)
    (dataAll : ∀ (d : ℕ) [NeZero d], d ∣ N → ModularPolynomialData d)
    (hsep : (((dataAll N (dvd_refl N)).Φ.map
        (Polynomial.mapRingHom (Int.castRingHom (ResidueField ↥A)))).map
      (algebraMap (Polynomial (ResidueField ↥A)) (RatFunc (ResidueField ↥A)))).Separable)
    (hpres : fm.SpDivPreservesPrincipal Ideal.Quotient.mk_surjective dataAll hsep)
    (hsq : Squarefree N) (hsym : EvalSymm (dataAll N (dvd_refl N)).Φ)
    (data : ModularPolynomialData ℓ) (hKr : KroneckerCongruence ℓ data)
    [IsCurveOver (ResidueField ↥A) (modularFunctionFieldC (ResidueField ↥A) N)] :
    letI := heckeModuleBar N
    ∃ (_ : Module HeckeAlg (Pic0 (ResidueField ↥A) (modularFunctionFieldC (ResidueField ↥A) N)))
      (D : JZeroGoodReductionSpecialization A ℓ hℓ.out N),
      D.sp = fm.spPic0 Ideal.Quotient.mk_surjective dataAll hsep ∧
      D.F = frobeniusPushforwardGeomLevelPic0OfIsCurveOver (ResidueField ↥A) N data hKr := by sorry
