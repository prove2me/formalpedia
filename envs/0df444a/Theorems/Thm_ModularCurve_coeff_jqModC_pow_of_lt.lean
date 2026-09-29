-- Prove2me | Theorems.Thm_ModularCurve_coeff_jqModC_pow_of_lt
-- name    : ModularCurve.coeff_jqModC_pow_of_lt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:49.598281+00:00
-- url     : https://prove2.me/theorems/29ce3c8f-0582-52a8-98cf-a811e40f47e0
-- title:
--   No coefficients below q⁻ᵇ in j(q)ᵇ
-- statement:
--   Let $K$ be a commutative ring, let $b$ be a natural number and let $m$ be an integer with $m < -b$. Here `jqModC K` is the element of the Laurent series field `LaurentSeries K` (Hahn series over $K$ with value group $\mathbb{Z}$) given by $\mathrm{single}(-1,1)$, the series $q^{-1}$, multiplied by the image under `HahnSeries.ofPowerSeries` of the power series `jNum` $= E_4^3 \cdot \eta$-unit-inverse $\in \mathbb{Z}[[q]]$ with its coefficients pushed into $K$ along the canonical ring homomorphism $\mathbb{Z} \to K$; that is, the $q$-expansion of the modular invariant $j$ read in $K((q))$. The assertion is that the coefficient of $q^m$ in the $b$-th power $(\mathtt{jqModC } K)^b$ vanishes. Equivalently, $(\mathtt{jqModC } K)^b$ lies in $q^{-b}\,K[[q]]$: it has a pole at $q=0$ of order at most $b$. No hypothesis beyond $m < -b$ is imposed; in particular $K$ may have characteristic $p$ or be non-reduced, and the case $b = 0$ is included.
--
--   This is the elementary statement that the $q$-expansion of $j$ has leading term $q^{-1}$, so that its powers have poles of bounded order, transported to an arbitrary coefficient ring. It underlies the degree and order bookkeeping for $q$-expansions of modular functions on $X_0(N)$, and is used, together with the companion computation of the coefficient in degree $-b$, to show that $j$ is transcendental over $K$ and that the order of `jqModC K` is $-1$; it is cited at several places where $q$-expansions of modular units and of level-$N$ analogues are compared.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_coeff_jqModC_pow_of_lt.lean

import Definitions.Def_ModularCurve_JqCoeff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve

theorem ModularCurve.coeff_jqModC_pow_of_lt (K : Type*) [CommRing K] {b : ℕ} {m : ℤ} (hm : m < -(b : ℤ)) :
    ((jqModC K) ^ b).coeff m = 0 := by sorry
