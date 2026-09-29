-- Prove2me | Theorems.Thm_ModularCurve_roots_fibrePoly
-- name    : ModularCurve.roots_fibrePoly
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:54.618386+00:00
-- url     : https://prove2.me/theorems/686f4915-849a-5997-8a18-d856d8867427
-- title:
--   Roots of the fibre polynomial: {a^ℓ}+ℓ·{a^{1/ℓ}}
-- statement:
--   Let $k$ be a field of characteristic a prime $\ell$ which is perfect in the sense that the $\ell$-power Frobenius is bijective, and let `data` be a `ModularPolynomialData ℓ`, that is, a bivariate integral polynomial $\Phi \in \mathbb{Z}[X][Y]$ (the outer variable being $Y$) together with the data that $\Phi$ is monic in $Y$, that its degree in $Y$ equals $\mathrm{dedekindPsi}\,\ell = \sum_{d \mid \ell,\ d \text{ squarefree}} \ell/d$, and that $\Phi$ vanishes when $X$ is evaluated at the $q$-expansion `jq` and $Y$ at `jqN ℓ`. Assume the Kronecker congruence `KroneckerCongruence ℓ data`: the coefficientwise reduction of $\Phi$ modulo $\ell$ equals $(X^{\ell} - Y)(X - Y^{\ell})$ in $(\mathbb{Z}/\ell)[X][Y]$. Then for every $a \in k$, the multiset of roots of the fibre polynomial $\mathrm{fibrePoly}\,\Phi\,a \in k[Y]$, obtained from $\Phi$ by casting its integer coefficients into $k$ and evaluating the inner variable $X$ at $a$, is $\{a^{\ell}\}$ together with $\ell$ copies of the unique $\ell$-th root $a^{1/\ell}$ of $a$ in $k$, the latter written as the image of $a$ under the inverse of the Frobenius equivalence of $k$.
--
--   This is the divisor-level form of the Eichler–Shimura congruence on the $j$-line at level $\ell$: over a perfect field of characteristic $\ell$ the fibre of the reduced modular correspondence over a point $a$ consists of the Frobenius image $a^{\ell}$ with multiplicity one and the Frobenius preimage $a^{1/\ell}$ with multiplicity $\ell$, so that $T_\ell = F + V$ on divisors. It is used by [`ModularCurve.placeSpecialization_exists_level_one_of_surjective`](thm.html#ModularCurve.placeSpecialization_exists_level_one_of_surjective).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_roots_fibrePoly.lean

import Mathlib
import Definitions.Def_ModularCurve_FibrePoly

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open Polynomial

theorem ModularCurve.roots_fibrePoly {k : Type*} [Field k] {ℓ : ℕ} [Fact ℓ.Prime]
    [CharP k ℓ] [PerfectRing k ℓ] (data : ModularCurve.ModularPolynomialData ℓ)
    (hK : ModularCurve.KroneckerCongruence ℓ data) (a : k) :
    (ModularCurve.fibrePoly data.Φ a).roots =
      {a ^ ℓ} + ℓ • {(frobeniusEquiv k ℓ).symm a} := by sorry
