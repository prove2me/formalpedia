-- Prove2me | Theorems.Thm_ModularCurve_PhiGen_splits_of_coeff_evalAtJ_eq
-- name    : ModularCurve.PhiGen.splits_of_coeff_evalAtJ_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.572352+00:00
-- url     : https://prove2.me/theorems/6cde1021-2e2d-529d-b0df-4dbbd8fd0215
-- title:
--   Descended coefficients force Φ to split into conjugates
-- statement:
--   Let $K$ be a field equipped with a $\mathbb{Q}$-algebra structure, let $\ell$ be a natural number carrying a `Fact` instance that it is prime, let $\zeta$ be a unit of $K$, and let $c \colon \mathbb{N} \to \mathbb{Q}((q))$ be a family of Laurent series over $\mathbb{Q}$. Assume `PhiGenDescends ℓ ζ c`, that is: for every $k$, the $k$-th coefficient of the product $\prod_{i \in \mathrm{Fin}(\ell+1)} \bigl(X - C(\mathrm{conj}\,\ell\,\zeta\,i)\bigr)$ over $K((q))$ — where $\mathrm{conj}\,\ell\,\zeta\,i$ is obtained from the image of the $j$-expansion $jq$ in $K((q))$ by the twist $q \mapsto \zeta^{ab}q$ followed by $q \mapsto q^{a^2}$, with $a = \ell,\ b = 0$ for $i = 0$ and $a = 1,\ b = i-1$ otherwise — equals the image of $c_k$ under $q \mapsto q^{\ell}$ followed by coefficientwise base change $\mathbb{Q} \to K$. Let `data` consist of a monic $\Phi \in \mathbb{Z}[X][Y]$ of $Y$-degree $\psi(\ell) = \ell + 1$ satisfying $\Phi(jq, \cdot)$ annihilating $jqN\ \ell$, and assume that for every $k$ the $k$-th $Y$-coefficient of $\Phi$, evaluated at $X = jq$, equals $c_k$. Then applying to the coefficients of $\Phi$ the ring homomorphism $X \mapsto jq$, followed by $q \mapsto q^{\ell}$ and by base change to $K$, yields exactly that product $\prod_i (X - C(\mathrm{conj}\,\ell\,\zeta\,i))$.
--
--   This is the modular equation for $X_0(\ell)$ read as a factorisation: the classical statement that $\Phi_\ell(X,Y)$, specialised at $X = j(q)$ and re-expanded in $q^{1/\ell}$-style coordinates, is the monic polynomial whose roots are the $\ell+1$ conjugates $j(q^{\ell^2})$ and $j(\zeta^{i}q)$. It feeds the symmetry and splitting statements [`ModularCurve.PhiGen.evalSymm_of_coeff_evalAtJ_eq`](thm.html#ModularCurve.PhiGen.evalSymm_of_coeff_evalAtJ_eq), [`ModularCurve.PhiGen.splits_of_prime`](thm.html#ModularCurve.PhiGen.splits_of_prime) and [`ModularCurve.exists_phiIrreducible_evalSymm`](thm.html#ModularCurve.exists_phiIrreducible_evalSymm).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PhiGen_splits_of_coeff_evalAtJ_eq.lean

import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_PhiGen

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve ModularCurve.PhiGen

theorem ModularCurve.PhiGen.splits_of_coeff_evalAtJ_eq {K : Type*} [Field K] [Algebra ℚ K] {ℓ : ℕ} [hℓ : Fact (Nat.Prime ℓ)] (ζ : Kˣ) {c : ℕ → LaurentSeries ℚ} (hc : PhiGenDescends ℓ ζ c) (data : ModularPolynomialData ℓ) (hcoeff : ∀ k, evalAtJ (data.Φ.coeff k) = c k) : data.Φ.map (((coeffEmb K).comp (qExpand ℚ ℓ)).comp evalAtJ) = phiProd ℓ (conj ℓ ζ) := by sorry
