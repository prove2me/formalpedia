-- Prove2me | Theorems.Thm_ModularCurve_aeval_jq_eq_zero
-- name    : ModularCurve.aeval_jq_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:49.598281+00:00
-- url     : https://prove2.me/theorems/6b297b57-a728-5c3d-8a7f-cf5ca651241c
-- title:
--   A rational polynomial vanishing at j(q) is zero
-- statement:
--   Let $p$ be a polynomial in one variable over $\mathbb{Q}$, and suppose that evaluating $p$ at the Laurent series `jq` gives $0$, that is, $p(\mathrm{jq}) = 0$ in the field of Laurent series `LaurentSeries ℚ` (Hahn series over $\mathbb{Q}$ with value group $\mathbb{Z}$), where the evaluation is the $\mathbb{Q}$-algebra map `Polynomial.aeval`. Here `jq` is the element $q^{-1}\cdot \mathrm{jNumQ}(q)$, obtained as the product of the Hahn series `HahnSeries.single (-1) 1` supported in degree $-1$ with coefficient $1$ and the image under `HahnSeries.ofPowerSeries` of `jNumQ`, the power series over $\mathbb{Q}$ got from the integral power series `jNum` by the coefficientwise ring map $\mathbb{Z} \to \mathbb{Q}$; thus `jq` is the formal $q$-expansion of the modular $j$-invariant. The conclusion is that $p = 0$. Equivalently, `jq` is transcendental over $\mathbb{Q}$ inside $\mathbb{Q}((q))$.
--
--   This is the basic transcendence statement underlying the construction of the modular function fields of $X_0(N)$ inside $\mathbb{Q}((q))$: the $q$-expansion of $j$ satisfies no algebraic relation over $\mathbb{Q}$. It is used for [`ModularCurve.transcendental_jq`](thm.html#ModularCurve.transcendental_jq) and, after substituting $q \mapsto q^N$, for [`ModularCurve.transcendental_jqN`](thm.html#ModularCurve.transcendental_jqN).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_aeval_jq_eq_zero.lean

import Definitions.Def_ModularCurve_X0

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve IntermediateField

theorem ModularCurve.aeval_jq_eq_zero {p : Polynomial ℚ} (hp : Polynomial.aeval jq p = 0) : p = 0 := by sorry
