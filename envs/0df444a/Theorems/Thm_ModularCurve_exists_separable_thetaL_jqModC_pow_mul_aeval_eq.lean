-- Prove2me | Theorems.Thm_ModularCurve_exists_separable_thetaL_jqModC_pow_mul_aeval_eq
-- name    : ModularCurve.exists_separable_thetaL_jqModC_pow_mul_aeval_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:51.361078+00:00
-- url     : https://prove2.me/theorems/c7d533c8-dc2d-5bb5-8868-9afe79145691
-- title:
--   Hasse invariant in the j-coordinate, characteristic p≥ 5
-- statement:
--   Let $p$ be a prime with $5\le p$ and let $K$ be a field of characteristic $p$. Work in the field $K((\mathsf q))$ of formal Laurent series, where $\bar\jmath=$ `jqModC K` is the product of the monomial $\mathsf q^{-1}$ with the power series obtained from `jNum` $=E_4^3\cdot$ `dedekindEtaUnitInv` $\in\mathbb Z[[\mathsf q]]$ by reducing its coefficients into $K$, and where $\theta=$ `thetaL K` is the $K$-linear operator $f\mapsto \mathsf q\,\mathrm d f/\mathrm d\mathsf q$, i.e. multiplication of the formal derivative by the monomial $\mathsf q$. The assertion is that there exist natural numbers $m,e_4,e_6$ and a polynomial $S\in K[X]$ such that $12m+4e_4+6e_6=p-1$ (truncated subtraction of naturals), $e_4\le 1$, $e_6\le 1$, $S$ is monic and separable with $\deg S=m$ and $S(0)\ne 0$, $S(1728)\ne 0$, and, with $S$ evaluated at $\bar\jmath$ through the $K$-algebra structure of $K((\mathsf q))$,
--   $$(\theta\bar\jmath)^{(p-1)/2}\,S(\bar\jmath)=(-1)^{(p-1)/2}\,\bar\jmath^{\,4m+e_4+2e_6}\,(\bar\jmath-1728)^{3m+e_4+e_6},$$
--   the exponent $(p-1)/2$ being natural-number division. No hypothesis of algebraic closure or perfection is imposed on $K$; the polynomial $S$ is produced over $K$ itself.
--
--   This is the $j$-coordinate form of the classical identity expressing the Hasse invariant in characteristic $p\ge 5$: the supersingular polynomial $S$ of degree $m=\lfloor p/12\rfloor$ appears together with the correction factors $\bar\jmath^{e_4}$ and $(\bar\jmath-1728)^{e_6}$ accounting for the elliptic points, written multiplicatively against the weight-two form $\theta\bar\jmath$. It feeds the later analysis of the Hasse root function on the relevant function fields, in particular the computation of ramification indices at points whose $j$-invariant is or is not supersingular, and the construction of a homomorphism on units from it.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_separable_thetaL_jqModC_pow_mul_aeval_eq.lean

import Mathlib
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_QExpansionDiff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve

theorem ModularCurve.exists_separable_thetaL_jqModC_pow_mul_aeval_eq
    (p : ℕ) [Fact p.Prime] (hp : 5 ≤ p) (K : Type*) [Field K] [CharP K p] :
    ∃ (m e₄ e₆ : ℕ) (S : Polynomial K),
      12 * m + 4 * e₄ + 6 * e₆ = p - 1 ∧ e₄ ≤ 1 ∧ e₆ ≤ 1 ∧
      S.Monic ∧ S.Separable ∧ S.natDegree = m ∧ S.eval 0 ≠ 0 ∧ S.eval 1728 ≠ 0 ∧
      thetaL K (jqModC K) ^ ((p - 1) / 2) * Polynomial.aeval (jqModC K) S =
        (-1) ^ ((p - 1) / 2) *
          (jqModC K ^ (4 * m + e₄ + 2 * e₆) * (jqModC K - 1728) ^ (3 * m + e₄ + e₆)) := by sorry
