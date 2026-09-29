-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_ord_residueFst_modularUnit_eq_mul_ord_jqModC_of_not_isAffineGeomPlace
-- name    : ModularCurve.PlaceSpecialization.ProlongationTuple.ord_residueFst_modularUnit_eq_mul_ord_jqModC_of_not_isAffineGeomPlace
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:45.66333+00:00
-- url     : https://prove2.me/theorems/ed707dd9-2d30-5027-9d38-a5454a1c5d9d
-- title:
--   Order of the reduced modular unit at non-affine places
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbb{Q}}$, a nonzero level $N$, and a field $k$ of characteristic $q$ together with a ring homomorphism $\mathrm{red} : A \to k$. Let `data` be a `ModularPolynomialData` for $q$, i.e. a monic $\Phi \in \mathbb{Z}[X][Y]$ of degree $\psi(q)$ annihilating the $q$-expansion datum, let `hKr` assert the Kronecker congruence $\Phi \bmod q = (X^q - Y)(X - Y^q)$ in the bivariate reduction, and let `hα`, `hβ` assert that the Hecke $\bar\alpha$- and $\bar\beta$-homomorphisms at level $N$ and prime $q$ over $\overline{\mathbb{Q}}$ are integral. Assume $q \nmid N$, let $P$ be a place specialisation `PlaceSpecialization A q N data hKr k red hα hβ` and $R$ a prolongation tuple over $P$. Let $u$ lie in `modularFunctionFieldBar (N * q)`, the base change to $\overline{\mathbb{Q}}$ of the full modular function field of level $Nq$ inside Laurent series, and suppose that, as a Laurent series, $u$ is the image under `coeffEmb` of $\Delta \cdot \Delta_q^{-1}$, the modular unit series at $q$; suppose further that $u$ lies in `R.R₁.integers`. Finally let $v$ be a place of `modularFunctionFieldC k N` over $k$ which is not an affine geometric place, i.e. for which at least one of `jGeomGen k N`, `jNGeomGen k N` fails to lie in the valuation subring of $v$. Then $\mathrm{ord}_v$ of the first residue `R.residue₁ ⟨u, h₁⟩` equals $(q-1)$ times $\mathrm{ord}_v$ of the element of `modularFunctionFieldC k N` given by `jqModC k`, the mod-$q$ $q$-expansion $q^{-1} + \dots$ of the $j$-invariant; here $\mathrm{ord}_v$ is minus the logarithm of the associated $\mathbb{Z}^{m0}$-valued adic valuation.
--
--   This is the cusp-order computation for the level-$q$ modular unit on the special fibre: away from the affine locus the reduction of $\Delta/\Delta_q$ is, up to units, a polynomial of degree $q-1$ in the reduced $j$-function, so its divisor is supported at the non-affine places with multiplicities $(q-1)$ times those of $j$. It feeds the construction of the divisor satisfying the one-sided laws for the modular unit in [`ModularCurve.PlaceSpecialization.ProlongationTuple.exists_divisor_oneSidedFst_laws_modularUnit`](thm.html#ModularCurve.PlaceSpecialization.ProlongationTuple.exists_divisor_oneSidedFst_laws_modularUnit).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_ord_residueFst_modularUnit_eq_mul_ord_jqModC_of_not_isAffineGeomPlace.lean

import Definitions.Def_ModularCurve_ProlongationTuple
import Definitions.Def_ModularCurve_ModularUnit
import Definitions.Def_ModularCurve_LaurentCoeff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option Elab.async false
set_option synthInstance.maxHeartbeats 400000
open AlgebraicCurve ModularCurve

theorem ModularCurve.PlaceSpecialization.ProlongationTuple.ord_residueFst_modularUnit_eq_mul_ord_jqModC_of_not_isAffineGeomPlace
    {q : ℕ} [Fact q.Prime]
    {A : ValuationSubring (AlgebraicClosure ℚ)} {N : ℕ} [NeZero N] {k : Type*} [Field k]
    [CharP k q] {red : A →+* k} {data : ModularPolynomialData q}
    {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) N q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q}
    (hqN : ¬ q ∣ N)
    (P : PlaceSpecialization A q N data hKr k red hα hβ)
    (R : ProlongationTuple P)
    (u : modularFunctionFieldBar (N * q))
    (hu : (u : LaurentSeries (AlgebraicClosure ℚ))
      = coeffEmb (AlgebraicClosure ℚ) (modularUnitSeries q))
    (h₁ : u ∈ R.R₁.integers)
    (v : Place k (modularFunctionFieldC k N)) (hv : ¬ IsAffineGeomPlace k N v) :
    v.ord (R.residue₁ ⟨u, h₁⟩) = ((q : ℤ) - 1) * v.ord ⟨jqModC k, jqModC_mem k N⟩ := by sorry
