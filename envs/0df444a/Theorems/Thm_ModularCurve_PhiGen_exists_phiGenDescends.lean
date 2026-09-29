-- Prove2me | Theorems.Thm_ModularCurve_PhiGen_exists_phiGenDescends
-- name    : ModularCurve.PhiGen.exists_phiGenDescends
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.572352+00:00
-- url     : https://prove2.me/theorems/418bc88b-897a-537e-9a6f-9ce9729e3520
-- title:
--   Descent of the coefficients of Φ_ℓ to ℚ((q))
-- statement:
--   Let $K$ be a field equipped with a $\mathbb{Q}$-algebra structure, let $\ell$ be a prime, and let $\zeta$ be a unit of $K$. Assume that $K$ is a finite Galois extension of $\mathbb{Q}$ and that the image of $\zeta$ in $K$ is a primitive $\ell$-th root of unity. The assertion is that there exists a family $c : \mathbb{N} \to \mathbb{Q}((q))$ of rational Laurent series with `PhiGenDescends ℓ ζ c`, that is: for every natural number $k$, the coefficient of $X^k$ in the monic polynomial $\prod_{i : \mathrm{Fin}(\ell+1)} (X - \mathrm{conj}\,\ell\,\zeta\,i) \in K((t))[X]$, whose roots are the $\ell+1$ series $\mathrm{conj}\,\ell\,\zeta\,i = \mathrm{cosetSubst}\ \zeta\ (\mathrm{cosetA}\,\ell\,i)\ (\mathrm{cosetB}\,\ell\,i)$ applied to the coefficientwise image in $K((t))$ of the series `jq`, is equal to the coefficientwise image under $\mathbb{Q} \to K$ of $\mathrm{qExpand}\ \mathbb{Q}\ \ell\ (c_k)$, the series obtained from $c_k$ by multiplying all exponents by $\ell$. Thus each coefficient of the product lies in the image of $\mathbb{Q}((q))$ under the substitution $q \mapsto t^{\ell}$ followed by base change to $K$; the family $c$ itself is only asserted to exist, with no normalisation or uniqueness claim.
--
--   This is the existence half of the construction of the modular polynomial $\Phi_\ell(j, Y)$ from the $\ell+1$ conjugate $q$-expansions: it records simultaneously that the elementary symmetric functions of the conjugates are series in $t^{\ell}$ and that they have rational coefficients. It feeds the assembly of the modular polynomial data for $X_0(\ell)$, in particular [`ModularCurve.exists_modularPolynomialData_evalSymm`](thm.html#ModularCurve.exists_modularPolynomialData_evalSymm), [`ModularCurve.ModularPolynomialData.weighted_support_le`](thm.html#ModularCurve.ModularPolynomialData.weighted_support_le) and [`ModularCurve.PhiGen.splits_of_prime`](thm.html#ModularCurve.PhiGen.splits_of_prime).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PhiGen_exists_phiGenDescends.lean

import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_PhiGen
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.FieldTheory.Galois.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve ModularCurve.PhiGen

theorem ModularCurve.PhiGen.exists_phiGenDescends {K : Type*} [Field K] [Algebra ℚ K] (ℓ : ℕ) [hℓ : Fact (Nat.Prime ℓ)] (ζ : Kˣ) [IsGalois ℚ K] [FiniteDimensional ℚ K] (hζ : IsPrimitiveRoot (ζ : K) ℓ) : ∃ c : ℕ → LaurentSeries ℚ, PhiGenDescends ℓ ζ c := by sorry
