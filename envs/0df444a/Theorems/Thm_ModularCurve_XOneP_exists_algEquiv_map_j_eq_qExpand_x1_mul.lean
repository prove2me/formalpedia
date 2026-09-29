-- Prove2me | Theorems.Thm_ModularCurve_XOneP_exists_algEquiv_map_j_eq_qExpand_x1_mul
-- name    : ModularCurve.XOneP.exists_algEquiv_map_j_eq_qExpand_x1_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:47.601084+00:00
-- url     : https://prove2.me/theorems/f9ae8c95-9f19-5d24-9b74-b3cef6f66291
-- title:
--   An L-automorphism of the X₁(Mp) function field sending j to j(qᵖ)
-- statement:
--   Let $p$ be a prime and $M$ a positive integer with $p \nmid M$, and let $L$ be a field of characteristic zero which is a $p$-th cyclotomic extension of $\mathbb{Q}$. Let $K$ be an intermediate field of the Laurent series field $L((q))$ over $L$, assumed equal to [`ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p))`](def/ModularCurve_LaurentCoeff.html#L103), that is, the subfield of $L((q))$ generated over $L$ by the image of the $q$-expansion function field `qExpFunctionFieldC ℚ (Gamma1 (M * p))` attached to $\Gamma_1(Mp)$ inside $\mathbb{Q}((q))$ under the coefficientwise ring embedding $\mathbb{Q}((q)) \to L((q))$ induced by $\mathbb{Q} \to L$. Let $j$ be an element of $K$ whose image in $L((q))$ is the coefficientwise image of [`ModularCurve.jq`](def/ModularCurve_X0.html#L157), the Laurent series $q^{-1}$ times the rational power series obtained from the integral series `jNum` by base change to $\mathbb{Q}$. The conclusion is that there exists an $L$-algebra automorphism $\sigma$ of $K$ such that the image of $\sigma(j)$ in $L((q))$ is the coefficientwise image of [`ModularCurve.qExpand ℚ p`](def/ModularCurve_X0.html#L25) applied to [`ModularCurve.jq`](def/ModularCurve_X0.html#L157), where `qExpand ℚ p` is the ring endomorphism of $\mathbb{Q}((q))$ given by multiplying all exponents by $p$, i.e. the substitution $q \mapsto q^p$. Thus $\sigma(j) = j(q^p)$.
--
--   This is the action on $q$-expansions of the partial Atkin–Lehner involution at $p$ on $X_1(Mp)$, realised over a $p$-th cyclotomic field $L$ as an $L$-automorphism of the function field viewed inside $L((q))$; on the Tate curve it corresponds to the isogeny $\mathrm{Tate}(q) \to \mathrm{Tate}(q)/\mu_p = \mathrm{Tate}(q^p)$, whence the effect $j \mapsto j(q^p)$ on the modular invariant. It feeds the subsequent statement combining this automorphism with the behaviour of the chart and comap data for $X_1(Mp)$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XOneP_exists_algEquiv_map_j_eq_qExpand_x1_mul.lean

import Mathlib
import Definitions.Def_ModularCurve_X1

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ModularCurve.XOneP.exists_algEquiv_map_j_eq_qExpand_x1_mul
    (p : ℕ) [Fact p.Prime] (M : ℕ) [NeZero M] (hpM : ¬ p ∣ M)
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L]
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L (ModularCurve.x1FunctionField (M * p)))
    (j : ↥K) (hj : ((j : LaurentSeries L)) = ModularCurve.coeffEmb L ModularCurve.jq)
    [NeZero p] :
    ∃ σ : ↥K ≃ₐ[L] ↥K,
      ((σ j : ↥K) : LaurentSeries L) = ModularCurve.coeffEmb L (ModularCurve.qExpand ℚ p ModularCurve.jq) := by sorry
