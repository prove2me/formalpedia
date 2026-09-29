-- Prove2me | Theorems.Thm_ModularCurve_ModularPolynomialData_separable_map_ratFunc_of_prime
-- name    : ModularCurve.ModularPolynomialData.separable_map_ratFunc_of_prime
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:42.499921+00:00
-- url     : https://prove2.me/theorems/4e504df0-1444-5ea2-8dd2-e4992bd71f99
-- title:
--   Separability of the modular polynomial over K(X) at prime level
-- statement:
--   Let $K$ be a field, let $N$ be a prime, and let `data` be a term of [`ModularCurve.ModularPolynomialData N`](def/ModularCurve_X0.html#L215), i.e. a polynomial $\Phi =$ `data.Φ` in $\mathbb{Z}[X][Y]$ which is monic in $Y$, whose degree in $Y$ equals `dedekindPsi N` $= \sum_{d \mid N,\ d \text{ squarefree}} N/d$ (so $N+1$ for prime $N$), and which satisfies `data.eval_eq_zero`: evaluating $\Phi$ by means of the ring homomorphism `evalAtJ` $\colon \mathbb{Z}[X] \to$ `LaurentSeries ℚ` determined by $X \mapsto$ `jq` on the coefficients, at the Laurent series `jqN N` in place of $Y$, gives $0$. Assume moreover that $N \cdot 1_K \neq 0$ in $K$. The conclusion is that the polynomial obtained from $\Phi$ by first applying the coefficientwise map $\mathbb{Z}[X] \to K[X]$ induced by $\mathbb{Z} \to K$, and then the inclusion of $K[X]$ into the rational function field `RatFunc K`, is separable as an element of $(\mathrm{RatFunc}\ K)[Y]$, that is, coprime to its own derivative.
--
--   This is the field-generic form of Igusa's separability statement for the modular polynomial at prime level: $\Phi_N(X,Y)$ stays separable in $Y$ over $K(X)$ whenever $N$ is invertible in $K$, covering both characteristic zero and $K = \overline{\mathbb{F}}_\ell$ with $\ell \nmid N$. It feeds the construction of the Hecke correspondence data on the fibres of the modular curve, being cited by [`ModularCurve.heckeInputsFibre_of_natCast_ne_zero`](thm.html#ModularCurve.heckeInputsFibre_of_natCast_ne_zero) and [`ModularCurve.heckeInputsFibre_of_prime`](thm.html#ModularCurve.heckeInputsFibre_of_prime).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_ModularPolynomialData_separable_map_ratFunc_of_prime.lean

import Mathlib
import Definitions.Def_ModularCurve_X0

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularCurve.ModularPolynomialData.separable_map_ratFunc_of_prime (K : Type*) [Field K] (N : ℕ) [Fact N.Prime] (data : ModularCurve.ModularPolynomialData N)
    (hNK : (N : K) ≠ 0) :
    ((data.Φ.map (Polynomial.mapRingHom (Int.castRingHom K))).map
      (algebraMap (Polynomial K) (RatFunc K))).Separable := by sorry
