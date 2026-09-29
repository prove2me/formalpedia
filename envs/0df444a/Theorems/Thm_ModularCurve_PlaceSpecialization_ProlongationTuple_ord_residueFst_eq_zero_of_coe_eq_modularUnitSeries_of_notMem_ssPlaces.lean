-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_ord_residueFst_eq_zero_of_coe_eq_modularUnitSeries_of_notMem_ssPlaces
-- name    : ModularCurve.PlaceSpecialization.ProlongationTuple.ord_residueFst_eq_zero_of_coe_eq_modularUnitSeries_of_notMem_ssPlaces
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:45.66333+00:00
-- url     : https://prove2.me/theorems/f579bb57-c7c3-51cb-83ac-5b1c869f2da6
-- title:
--   Reduced modular unit has order zero at ordinary affine places
-- statement:
--   Fix a prime $q$, an integer $N \ge 1$, a valuation subring $A$ of $\overline{\mathbb Q}$, an algebraically closed field $k$ of characteristic $q$ and a ring homomorphism $red : A \to k$. Let `data` consist of a monic polynomial $\Phi \in \mathbb Z[X][Y]$ of degree $\psi(q)$ annihilating the $q$-th modular $\mathsf q$-expansion pair, let `hKr` assert the Kronecker congruence that the bivariate reduction of $\Phi$ modulo $q$ equals $(C X^{q}-X)(C X-X^{q})$, and let `hα`, `hβ` assert that the two Hecke homomorphisms `heckeAlphaBar` and `heckeBetaBar` at level $N$ and prime $q$ over $\overline{\mathbb Q}$ are integral. Let $P$ be a place specialisation over these data and $R$ a prolongation tuple over $P$. Let $u$ be an element of `modularFunctionFieldBar (N * q)`, the base change to $\overline{\mathbb Q}$ of the full level-$Nq$ modular function field inside $\overline{\mathbb Q}$-Laurent series, whose underlying Laurent series is the coefficientwise image of the modular unit series $\Delta \cdot \Delta_{q}^{-1}$ under $\mathbb Q \to \overline{\mathbb Q}$, and assume $u$ lies in the integers `R.R₁.integers` of the first prolongation, with witness $h_1$. Let $v$ be a place of `modularFunctionFieldC k N` $= k(\,j, j_N\,)$, i.e. a proper valuation subring containing $k$ whose ring is a principal ideal ring, such that both geometric generators `jGeomGen k N` and `jNGeomGen k N` lie in that valuation subring, and assume $v$ is not a supersingular place for $q$ and $N$ over $k$. Then the first residue `R.residue₁ ⟨u, h₁⟩` has order $0$ at $v$, the order being minus the logarithm of the $\mathbb Z^{\mathsf m 0}$-valued adic valuation attached to $v$.
--
--   This is the assertion that the reduction of the modular unit $\Delta(\tau)/\Delta(q\tau)$ on the level-$N$ special fibre in characteristic $q$ has neither zero nor pole away from the cusps and the supersingular points: its divisor is concentrated there. It is used in the construction of divisors satisfying the one-sided first-prolongation laws for this modular unit, and in the determination of the cusp law at $\infty$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_ord_residueFst_eq_zero_of_coe_eq_modularUnitSeries_of_notMem_ssPlaces.lean

import Definitions.Def_ModularCurve_ProlongationTuple
import Definitions.Def_ModularCurve_ModularUnit

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option Elab.async false
set_option synthInstance.maxHeartbeats 400000
open HahnSeries ModularCurve AlgebraicCurve IsLocalRing

theorem ModularCurve.PlaceSpecialization.ProlongationTuple.ord_residueFst_eq_zero_of_coe_eq_modularUnitSeries_of_notMem_ssPlaces
    {q : ℕ} [Fact q.Prime]
    {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N] {k : Type*} [Field k]
    [CharP k q] {red : A →+* k} {data : ModularPolynomialData q}
    {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q} [IsAlgClosed k] [DecidableEq k]
    (P : PlaceSpecialization A q N data hKr k red hα hβ)
    (R : ProlongationTuple P)
    (u : modularFunctionFieldBar (N * q))
    (hu : (u : LaurentSeries (AlgebraicClosure ℚ))
      = coeffEmb (AlgebraicClosure ℚ) (modularUnitSeries q)) (h₁ : u ∈ R.R₁.integers)
    (v : Place k (modularFunctionFieldC k N))
    (haff : IsAffineGeomPlace k N v) (hord : v ∉ ssPlaces q N k) :
    v.ord (R.residue₁ ⟨u, h₁⟩) = 0 := by sorry
