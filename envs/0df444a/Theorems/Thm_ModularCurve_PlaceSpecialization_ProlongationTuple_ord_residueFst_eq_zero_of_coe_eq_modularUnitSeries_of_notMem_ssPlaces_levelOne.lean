-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_ord_residueFst_eq_zero_of_coe_eq_modularUnitSeries_of_notMem_ssPlaces_levelOne
-- name    : ModularCurve.PlaceSpecialization.ProlongationTuple.ord_residueFst_eq_zero_of_coe_eq_modularUnitSeries_of_notMem_ssPlaces_levelOne
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:45.66333+00:00
-- url     : https://prove2.me/theorems/0c58e74d-b3b2-57e4-9efd-5e053b5e6cff
-- title:
--   Modular unit residue is a unit at non-supersingular affine places
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbb Q}$, an algebraically closed field $k$ of characteristic $q$ and a ring homomorphism $\mathrm{red} : A \to k$; fix furthermore a `ModularPolynomialData q`, i.e. a monic $\Phi \in \mathbb Z[X][Y]$ of degree $\psi(q)$ annihilating the pair of $\mathsf q$-expansions $j$, $j(\mathsf q^q)$, together with a proof `hKr` that its bivariate reduction modulo $q$ equals $(C(X)^q - X)\,(C(X) - X^q)$, and proofs $h\alpha$, $h\beta$ that the two Hecke homomorphisms $\overline{\alpha}$, $\overline{\beta}$ over $\overline{\mathbb Q}$ at level $1$ and prime $q$ are integral. Let $P$ be a place specialization of these data at level $N = 1$ and $R$ a prolongation tuple over $P$. Let $u$ be an element of `modularFunctionFieldBar (1 * q)`, the base change to $\overline{\mathbb Q}$ inside $\mathrm{LaurentSeries}(\overline{\mathbb Q})$ of the full modular function field of level $q$, whose underlying Laurent series is the coefficientwise image of the modular unit $\Delta \cdot \Delta_q^{-1}$, and assume $u$ lies in the integers of the first regular prolongation $R_1$. Let $v$ be a place of `modularFunctionFieldC k 1`, the subfield of $\mathrm{LaurentSeries}(k)$ generated over $k$ by $j$ and $j_1$, such that both geometric generators $j$ and $j_N$ at level $1$ lie in the valuation subring of $v$ (affineness), and assume $v$ is not a supersingular place for $q$ at level $1$ over $k$. Then the order of vanishing at $v$ of the first residue $R.\mathrm{residue}_1(u)$, computed as minus the logarithm of the associated adic valuation, is $0$.
--
--   This is the statement that the reduction of the modular unit $\Delta(\tau)/\Delta(q\tau)$ on the first (identity) component of the special fibre of $X_0(q)$ is a unit away from the supersingular points and the cusp: its divisor is supported on the supersingular locus. It supplies the non-supersingular half of the one-sided regularity laws `regularityLawFst_oneSided_levelOne` and `regularityLawSnd_oneSided_levelOne` for the two prolongations.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_ord_residueFst_eq_zero_of_coe_eq_modularUnitSeries_of_notMem_ssPlaces_levelOne.lean

import Definitions.Def_ModularCurve_ProlongationTuple
import Definitions.Def_ModularCurve_ModularUnit

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option Elab.async false
set_option synthInstance.maxHeartbeats 400000
open HahnSeries ModularCurve AlgebraicCurve IsLocalRing

theorem ModularCurve.PlaceSpecialization.ProlongationTuple.ord_residueFst_eq_zero_of_coe_eq_modularUnitSeries_of_notMem_ssPlaces_levelOne
    {q : ℕ} [Fact q.Prime]
    {A : ValuationSubring (AlgebraicClosure ℚ)} {k : Type*} [Field k]
    [CharP k q] {red : A →+* k} {data : ModularPolynomialData q}
    {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q} [IsAlgClosed k] [DecidableEq k]
    (P : PlaceSpecialization A q 1 data hKr k red hα hβ)
    (R : ProlongationTuple P)
    (u : modularFunctionFieldBar (1 * q))
    (hu : (u : LaurentSeries (AlgebraicClosure ℚ))
      = coeffEmb (AlgebraicClosure ℚ) (modularUnitSeries q)) (h₁ : u ∈ R.R₁.integers)
    (v : Place k (modularFunctionFieldC k 1))
    (haff : IsAffineGeomPlace k 1 v) (hord : v ∉ ssPlaces q 1 k) :
    v.ord (R.residue₁ ⟨u, h₁⟩) = 0 := by sorry
