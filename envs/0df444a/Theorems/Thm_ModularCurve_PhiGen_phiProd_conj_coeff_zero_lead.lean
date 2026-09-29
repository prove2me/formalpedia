-- Prove2me | Theorems.Thm_ModularCurve_PhiGen_phiProd_conj_coeff_zero_lead
-- name    : ModularCurve.PhiGen.phiProd_conj_coeff_zero_lead
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.572352+00:00
-- url     : https://prove2.me/theorems/df8372d0-9499-58e3-ae67-455f2247f76d
-- title:
--   Leading t-coefficient of the constant term of Φ_ℓ
-- statement:
--   Let $K$ be a field equipped with a $\mathbb{Q}$-algebra structure, let $\ell$ be a prime, and let $\zeta$ be a unit of $K$ whose underlying element is a primitive $\ell$-th root of unity. For each $i \in \mathrm{Fin}(\ell+1)$ put $a_i = \ell$, $b_i = 0$ if $i = 0$ and $a_i = 1$, $b_i = i-1$ otherwise, and let `conj ℓ ζ i` be the Laurent series over $K$ obtained from the rational Laurent series `jq`, transported coefficientwise to $K$ along $\mathbb{Q} \to K$ by `coeffEmb`, by applying the twisting homomorphism `qTwist (ζ ^ (a_i * b_i))` followed by the substitution homomorphism `qExpand K (a_i * a_i)`. Let `phiProd ℓ (conj ℓ ζ)` be the one-variable polynomial $\prod_{i \in \mathrm{Fin}(\ell+1)} (X - C(\mathrm{conj}\ \ell\ \zeta\ i))$ over `LaurentSeries K`. The assertion is that its degree-$0$ coefficient, a Laurent series over $K$, has Hahn-series coefficient equal to $1$ at the exponent $-(\ell^2+\ell)$.
--
--   This records the normalisation of the constant term of the generic modular polynomial $\Phi_\ell$ in the $q$-expansion model: the product of the $\ell+1$ conjugates, taken with the sign $(-1)^{\ell+1}$ coming from expanding the product, has leading term exactly $t^{-(\ell^2+\ell)}$. It is used in the control of the weighted support of the modular polynomial data ([`ModularCurve.ModularPolynomialData.weighted_support_le`](thm.html#ModularCurve.ModularPolynomialData.weighted_support_le)) and in [`ModularCurve.PhiGen.evalSymm_of_coeff_evalAtJ_eq`](thm.html#ModularCurve.PhiGen.evalSymm_of_coeff_evalAtJ_eq).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PhiGen_phiProd_conj_coeff_zero_lead.lean

import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_PhiGen
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve ModularCurve.PhiGen

theorem ModularCurve.PhiGen.phiProd_conj_coeff_zero_lead {K : Type*} [Field K] [Algebra ℚ K] (ℓ : ℕ) [hℓ : Fact (Nat.Prime ℓ)] (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) ℓ) : ((phiProd ℓ (conj ℓ ζ)).coeff 0).coeff (-((ℓ * ℓ + ℓ : ℕ) : ℤ)) = 1 := by sorry
