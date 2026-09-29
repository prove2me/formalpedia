-- Prove2me | Theorems.Thm_ModularCurve_modularPolynomial_eval_jInt_jQuotVelu_eq_zero
-- name    : ModularCurve.modularPolynomial_eval_jInt_jQuotVelu_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.624895+00:00
-- url     : https://prove2.me/theorems/8e0cd964-8239-5985-bcd4-2c727df2908b
-- title:
--   Modular polynomial vanishes at j(W) and j(W/⟨ Q⟩)
-- statement:
--   Fix a natural number $p$ (nonzero as a typeclass hypothesis) which is prime and different from $2$, and a modular-polynomial datum `data` of level $p$: a polynomial $\Phi \in \mathbb{Z}[X][Y]$ which is monic, of degree in $Y$ equal to $\sum_{d \mid p,\ d \text{ squarefree}} p/d$, and which satisfies the $q$-expansion identity obtained by substituting the Laurent series $j(q)$ for $X$ and $j(q^p)$ for $Y$. Let $W$ be a Weierstrass curve over $\mathbb{Z}$ with $\Delta_W \neq 0$, and let $\ell$ be a prime with $\ell \mid \Delta_W$ and $\ell \nmid c_4(W)$, so that $W$ is multiplicative at $\ell$. Let $Q$ be a point of the base change of $W$ to $\overline{\mathbb{Q}}$ (the algebraic closure of $\mathbb{Q}$) which is fixed by every $\mathbb{Q}$-algebra automorphism $\sigma$ of $\overline{\mathbb{Q}}$ and has exact additive order $p$. The conclusion is that $\Phi$ vanishes when $X$ is specialised to $c_4(W)^3/\Delta_W \in \overline{\mathbb{Q}}$ and $Y$ to $c_4(V)^3/\Delta_V \in \overline{\mathbb{Q}}$, where $V$ is the Vélu quotient of the base-changed curve by the finite set of coordinate pairs of the multiples $k \cdot Q$ for $1 \le k \le p/2$ (natural-number division, i.e. $k \le (p-1)/2$); explicitly $V$ has the same $a_1, a_2, a_3$ as the base change, with $a_4$ replaced by $a_4 - 5\sum_S t$ and $a_6$ by $a_6 - b_2\sum_S t - 7\sum_S w$ over that set $S$.
--
--   This is the classical relation, going back to Kronecker, that the pair of $j$-invariants of a curve and of its quotient by a cyclic subgroup of order $p$ is a root of the modular polynomial of level $p$, here in the integral form needed for curves with multiplicative reduction and a rational $p$-torsion point. It is the first of the inputs to [`ModularCurve.moduliPointExists_jQuotVelu_of_mult_two`](thm.html#ModularCurve.moduliPointExists_jQuotVelu_of_mult_two), which produces a point of the level-$p$ modular curve over the pair $(j(W), j(W/\langle Q\rangle))$, and it is also used by [`ModularCurve.modularPolynomial_rootMultiplicity_jQuotVelu_eq_one`](thm.html#ModularCurve.modularPolynomial_rootMultiplicity_jQuotVelu_eq_one).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_modularPolynomial_eval_jInt_jQuotVelu_eq_zero.lean

import Mathlib
import Definitions.Def_ModularCurve_MazurStepThreeInputs
import Definitions.Def_WeierstrassCurve_Velu
import Definitions.Def_WeierstrassCurve_OddOrderSummingSet

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassCurve WeierstrassCurve.Affine

theorem ModularCurve.modularPolynomial_eval_jInt_jQuotVelu_eq_zero
    (p : ℕ) [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (data : ModularCurve.ModularPolynomialData p)
    (W : WeierstrassCurve ℤ) (hΔ : W.Δ ≠ 0)
    {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓΔ : (ℓ : ℤ) ∣ W.Δ) (hℓc₄ : ¬ (ℓ : ℤ) ∣ W.c₄)
    (Q : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point)
    (hQfix : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, σ • Q = Q)
    (hQord : addOrderOf Q = p) :
    data.Φ.eval₂ (Polynomial.aeval (R := ℤ) (ModularCurve.jInt W)).toRingHom
      (let Wb := (W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)
       let V := Wb.veluQuotient (Wb.oddOrderSummingSet Q (addOrderOf Q / 2))
       (V.c₄ : AlgebraicClosure ℚ) ^ 3 / (V.Δ : AlgebraicClosure ℚ)) = 0 := by sorry
