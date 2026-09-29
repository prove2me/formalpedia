-- Prove2me | Theorems.Thm_ModularCurve_moduliPointExists_jQuotVelu_of_mult_two
-- name    : ModularCurve.moduliPointExists_jQuotVelu_of_mult_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.624895+00:00
-- url     : https://prove2.me/theorems/e17a8404-4001-5aa5-8c36-be9b1cd76994
-- title:
--   Rational moduli place on X₀(p) at a Vélu quotient
-- statement:
--   Let $p$ be a natural number with `NeZero p`, assumed prime and different from $2$, and let $W$ be a Weierstrass curve over $\mathbb{Z}$ with $\Delta(W)\neq 0$ which is multiplicative at $2$ in the sense that $2\mid\Delta(W)$ and $2\nmid c_4(W)$. Let $Q$ be a point of the base change of $W$ (first mapped to $\mathbb{Q}$ by `Int.castRingHom ℚ`, then base changed to $\overline{\mathbb{Q}}=$ `AlgebraicClosure ℚ`) which is fixed by every $\sigma\in\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ for the Galois action on points, and whose additive order `addOrderOf Q` is exactly $p$. The conclusion asserts the existence of a place $x$ of `modularFunctionFieldBar p` — the project's field $\overline{\mathbb{Q}}\cdot F$, where $F=$ `modularFunctionFieldFull p` is the subfield of $\mathbb{Q}((q))$ generated over $\mathbb{Q}$ by the project's `divisorExpansions p`, base changed inside `LaurentSeries (AlgebraicClosure ℚ)` — with four properties: (i) $x$ has degree $1$ over $\overline{\mathbb{Q}}$; (ii) $x$ is fixed by the semilinear action `arithmeticGalois (modularFunctionFieldFull p) σ` of every $\sigma\in\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$; (iii) the order of $x$ at `jBar p` minus the constant $j_{\mathbb{Z}}(W):=c_4(W)^3/\Delta(W)$, computed in $\overline{\mathbb{Q}}$ via `jInt`, is positive; (iv) the order of $x$ at `jpBar p` (the $q\mapsto q^p$ expansion of $j$) minus the constant $V.c_4^{\,3}/V.\Delta$ is positive, where $V$ is the Vélu curve `veluQuotient` of the base change $W_{\overline{\mathbb{Q}}}$ along the finite set `oddOrderSummingSet Q (addOrderOf Q / 2)` $=\{\,(\text{coordinates of }kQ) : 1\le k\le (p-1)/2\,\}$; this last quotient is Lean's total division, so it would read $0$ if $V.\Delta$ vanished, which under the hypotheses it does not. Thus $x$ is a $\mathbb{Q}$-rational degree-one place at which the two coordinate functions take the values $j(W)$ and $j(W_{\overline{\mathbb{Q}}}/\langle Q\rangle)$.
--
--   Classically this is the assertion, used in Step 3 of Mazur's argument (Mazur, Publ. Math. IHÉS 47 (1977), III §5), that a pair consisting of an elliptic curve over $\mathbb{Q}$ and a rational subgroup of order $p$ determines a rational point of $X_0(p)$, here realised as a Galois-stable degree-one place of the function field of $X_0(p)$ over $\overline{\mathbb{Q}}$ whose $j$-coordinates are $j(W)$ and $j(W/\langle Q\rangle)$. Compared with the project's predicate `ModuliPointExists` in `ModularCurve_MazurStepThreeInputs`, the shape differs: the function `jQuot` is fixed to be the explicit Vélu expression $V.c_4^{\,3}/V.\Delta$, and the hypothesis that $W$ is multiplicative at every prime dividing $\Delta(W)$ is replaced by the single local hypothesis at $2$ ($2\mid\Delta$, $2\nmid c_4$), together with $p\neq 2$. It is cited in [`WeierstrassCurve.mazurStepThree_not_inZeroComponentAt`](thm.html#WeierstrassCurve.mazurStepThree_not_inZeroComponentAt), the per-prime form of Mazur's Step 3.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_moduliPointExists_jQuotVelu_of_mult_two.lean

import Mathlib
import Definitions.Def_ModularCurve_MazurStepThreeInputs
import Definitions.Def_WeierstrassCurve_Velu
import Definitions.Def_WeierstrassCurve_OddOrderSummingSet

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassCurve WeierstrassCurve.Affine AlgebraicCurve

theorem ModularCurve.moduliPointExists_jQuotVelu_of_mult_two
    (p : ℕ) [NeZero p] (hp : p.Prime) (hp2 : p ≠ 2)
    (W : WeierstrassCurve ℤ) (hΔ : W.Δ ≠ 0)
    (h2Δ : (2 : ℤ) ∣ W.Δ) (h2c₄ : ¬ (2 : ℤ) ∣ W.c₄)
    (Q : ((W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)).Point)
    (hQfix : ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, σ • Q = Q)
    (hQord : addOrderOf Q = p) :
    ∃ x : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar p),
      x.deg = 1 ∧
      (∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
          arithmeticGalois (modularFunctionFieldFull p) σ • x = x) ∧
      0 < x.ord (jBar p - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar p) (jInt W)) ∧
      0 < x.ord (jpBar p - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar p)
            (let Wb := (W.map (Int.castRingHom ℚ))⁄(AlgebraicClosure ℚ)
             let V := Wb.veluQuotient (Wb.oddOrderSummingSet Q (addOrderOf Q / 2))
             (V.c₄ : AlgebraicClosure ℚ) ^ 3 / (V.Δ : AlgebraicClosure ℚ))) := by sorry
