-- Prove2me | Theorems.Thm_ModularCurve_exists_coeffMap_eq_of_isIntegralElem_of_exists_eq_div_of_injective
-- name    : ModularCurve.exists_coeffMap_eq_of_isIntegralElem_of_exists_eq_div_of_injective
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.209688+00:00
-- url     : https://prove2.me/theorems/0da273fa-cc2b-5a4d-a53c-683190232f01
-- title:
--   Integral q-expansions: integrality over R((q)) forces R-coefficients
-- statement:
--   Let $R$ be a commutative ring which is a domain and a principal ideal ring (i.e. a principal ideal domain), let $K$ be a field, and let $\varphi\colon R \to K$ be an injective ring homomorphism. Write $\mathrm{coeffMap}\,\varphi$ for the ring homomorphism $R((q)) \to K((q))$ on Laurent series obtained by applying $\varphi$ to each coefficient (the map `coeffMap`, defined as $x \mapsto x.\mathrm{map}\,\varphi$ on Hahn series over $\mathbb{Z}$ with the evident ring-homomorphism structure). Let $y \in K((q))$ and assume two things: first, that $y$ is a quotient $\mathrm{coeffMap}\,\varphi(a)/\mathrm{coeffMap}\,\varphi(b)$ for some $a, b \in R((q))$ with $b \neq 0$; second, that $y$ is an integral element for $\mathrm{coeffMap}\,\varphi$, that is, there is a monic polynomial with coefficients in $R((q))$ whose evaluation at $y$ along $\mathrm{coeffMap}\,\varphi$ vanishes. The conclusion is that $y$ lies in the image: there exists $c \in R((q))$ with $\mathrm{coeffMap}\,\varphi(c) = y$, so every coefficient of $y$ lies in $\varphi(R)$.
--
--   This is the Gauss-lemma half of the integral $q$-expansion principle: a Laurent series over $K$ that is a ratio of series with coefficients in $R$ and is integral over $R((q))$ already has coefficients in $R$. It is used in the passage from $q$-expansions over a field to integral models of modular curves, being cited in the treatment of the modular localised algebra in characteristic $p$ and in the identification of chart algebras of the two-chart integral models.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_coeffMap_eq_of_isIntegralElem_of_exists_eq_div_of_injective.lean

import Mathlib
import Definitions.Def_ModularCurve_LaurentCoeff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open ModularCurve

theorem ModularCurve.exists_coeffMap_eq_of_isIntegralElem_of_exists_eq_div_of_injective
    {R : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    {K : Type*} [Field K] (φ : R →+* K) (hφ : Function.Injective φ)
    (y : LaurentSeries K)
    (hy : ∃ a b : LaurentSeries R, b ≠ 0 ∧ y = coeffMap φ a / coeffMap φ b)
    (hint : (coeffMap φ).IsIntegralElem y) :
    ∃ c : LaurentSeries R, coeffMap φ c = y := by sorry
