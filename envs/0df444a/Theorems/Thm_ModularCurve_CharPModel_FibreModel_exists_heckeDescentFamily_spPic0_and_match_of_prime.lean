-- Prove2me | Theorems.Thm_ModularCurve_CharPModel_FibreModel_exists_heckeDescentFamily_spPic0_and_match_of_prime
-- name    : ModularCurve.CharPModel.FibreModel.exists_heckeDescentFamily_spPic0_and_match_of_prime
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:12.70306+00:00
-- url     : https://prove2.me/theorems/11c28033-317c-5241-bc8f-06b0d34a6307
-- title:
--   Hecke descent along the fibre specialisation, Eichler–Shimura at ℓ
-- statement:
--   Let $N$ be a nonzero natural number which is prime, and assume the operators $\mathrm{heckeOperatorBar}$ commute pairwise on $J =$ `JZero N`, the group $\mathrm{Pic}^0$ (degree-zero divisors modulo principal divisors) of the base-changed modular function field of level $N$ over $\overline{\mathbb{Q}}$. Let $\ell$ be a prime with $\ell \nmid N$, let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ with $\ell$ a non-unit of $A$, and let its residue field have characteristic $\ell$. Fix a `FibreModel` `fm` of level $N$ over $A$ with values in that residue field along the residue map, a cusp chart `cc` for it, and a family `dataAll` assigning to each divisor $d \mid N$ a modular polynomial datum; assume the image of $\Phi_N$ in $\mathrm{RatFunc}$ of the residue field is separable, that `fm.SpDivPreservesPrincipal` holds for this data (so the divisor specialisation sends degree-zero divisors to degree-zero divisors and principal ones to principal ones, whence `fm.spPic0` is the induced homomorphism $J \to \mathrm{Pic}^0$ of the special fibre), that $N$ is squarefree, and that $\Phi_N$ satisfies `EvalSymm`. Fix further a modular polynomial datum `data` at $\ell$ satisfying the Kronecker congruence, and assume the special-fibre function field is a curve over the residue field. Then, for the `heckeModuleBar N` action of $\mathrm{HeckeAlg} = \mathbb{Z}[X_q : q \text{ prime}]$ on $J$, there is a family $T'$ of $\mathbb{Z}$-linear endomorphisms of $\mathrm{Pic}^0$ of the special fibre, indexed by the primes, such that $T'_q \circ \mathrm{sp} = \mathrm{sp} \circ X_q$ for every prime $q$ and every $x \in J$, and such that $T'_\ell$ is the geometric fibre Hecke operator `heckeFibreGeomLevelPic0OfIsCurveOver` attached to `data` and the Kronecker congruence.
--
--   This is the descent of the full Hecke family along the specialisation of $J_0(N)$ to the Jacobian of the special fibre at a place above $\ell$, together with the identification of the descended operator at $\ell$ with the Frobenius-plus-transpose operator supplied by the Kronecker congruence, i.e. the Eichler–Shimura relation in this setting. It is the prime-level form of the statement, and feeds the construction of a good-reduction specialisation of $J_0(N)$ compatible with the Hecke action.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_CharPModel_FibreModel_exists_heckeDescentFamily_spPic0_and_match_of_prime.lean

import Definitions.Def_ModularCurve_SpecializationMap
import Definitions.Def_ModularCurve_FibreModelCuspChart
import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_ModularCurve_CharLFrobeniusGeomLevel
import Definitions.Def_ValuationSubring_ReduceAt

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve ModularCurve.CharPModel AlgebraicCurve IsLocalRing
set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem ModularCurve.CharPModel.FibreModel.exists_heckeDescentFamily_spPic0_and_match_of_prime
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
    ∃ T' : Nat.Primes → Module.End ℤ
        (Pic0 (ResidueField ↥A) (modularFunctionFieldC (ResidueField ↥A) N)),
      (∀ (q : Nat.Primes) (x : JZero N),
          T' q (fm.spPic0 Ideal.Quotient.mk_surjective dataAll hsep x)
            = fm.spPic0 Ideal.Quotient.mk_surjective dataAll hsep (heckeGen q • x))
      ∧ T' ⟨ℓ, hℓ.out⟩
          = (heckeFibreGeomLevelPic0OfIsCurveOver (ResidueField ↥A) N data hKr).toIntLinearMap := by sorry
