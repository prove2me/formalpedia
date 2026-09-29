-- Prove2me | Theorems.Thm_ModularCurve_modularPolynomial_rootMultiplicity_jQuotVelu_eq_one
-- name    : ModularCurve.modularPolynomial_rootMultiplicity_jQuotVelu_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.624895+00:00
-- url     : https://prove2.me/theorems/9827a685-87a3-5815-9eed-ddf736043754
-- title:
--   Simple root of Φₚ at the Vélu quotient j-invariant
-- statement:
--   Let $p$ be a nonzero natural number which is prime and different from $2$, and let `data` be a modular-polynomial datum of level $p$: a polynomial $\Phi \in \mathbb{Z}[X][Y]$ which is monic in $Y$, of degree $\sum_{d \mid p,\ d \text{ squarefree}} p/d$, and which annihilates the pair $(j, j_p)$ of $q$-expansions in the Laurent series over $\mathbb{Q}$. Let $W$ be a Weierstrass curve over $\mathbb{Z}$ with $\Delta \ne 0$, with $2 \mid \Delta$ and $2 \nmid c_4$, and let $Q$ be a point of the base change of $W$ to $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ`, fixed by every $\mathbb{Q}$-algebra automorphism of $\overline{\mathbb{Q}}$ and of exact additive order $p$. Form $V$, the Vélu quotient of the base-changed curve by the finite set of coordinate pairs of the multiples $k \cdot Q$ for $1 \le k \le p/2$ (so $a_1, a_2, a_3$ unchanged, $a_4 \mapsto a_4 - 5\,T$, $a_6 \mapsto a_6 - b_2 T - 7\,W$ for the Vélu sums $T, W$ over that set). Then the polynomial in $\overline{\mathbb{Q}}[Y]$ obtained from $\Phi$ by evaluating its coefficients at $c_4(W)^3/\Delta(W) \in \overline{\mathbb{Q}}$ has root multiplicity exactly $1$ at $c_4(V)^3/\Delta(V)$.
--
--   This is the uniqueness (simple-root) input of the moduli dictionary on the elliptic-curve side of Mazur's Step 3: the $j$-invariant of the Vélu quotient $W/\langle Q \rangle$ is a simple root of $\Phi_p(j(W), Y)$, the multiplicative-reduction hypotheses at $2$ serving to exclude the extra endomorphisms that would produce multiple roots. It is used by [`ModularCurve.moduliPointExists_jQuotVelu_of_mult_two`](thm.html#ModularCurve.moduliPointExists_jQuotVelu_of_mult_two).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_modularPolynomial_rootMultiplicity_jQuotVelu_eq_one.lean

import Mathlib
import Definitions.Def_ModularCurve_MazurStepThreeInputs
import Definitions.Def_WeierstrassCurve_Velu
import Definitions.Def_WeierstrassCurve_OddOrderSummingSet

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassCurve WeierstrassCurve.Affine

theorem ModularCurve.modularPolynomial_rootMultiplicity_jQuotVelu_eq_one
    (p : ℕ) [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (data : ModularCurve.ModularPolynomialData p)
    (W : WeierstrassCurve ℤ) (hΔ : W.Δ ≠ 0)
    (h2Δ : (2 : ℤ) ∣ W.Δ) (h2c₄ : ¬ (2 : ℤ) ∣ W.c₄)
    (Q : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point)
    (hQfix : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, σ • Q = Q)
    (hQord : addOrderOf Q = p) :
    (data.Φ.map (Polynomial.aeval (R := ℤ) (ModularCurve.jInt W)).toRingHom).rootMultiplicity
      (let Wb := (W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)
       let V := Wb.veluQuotient (Wb.oddOrderSummingSet Q (addOrderOf Q / 2))
       (V.c₄ : AlgebraicClosure ℚ) ^ 3 / (V.Δ : AlgebraicClosure ℚ)) = 1 := by sorry
