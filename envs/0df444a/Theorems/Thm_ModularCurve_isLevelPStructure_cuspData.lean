-- Prove2me | Theorems.Thm_ModularCurve_isLevelPStructure_cuspData
-- name    : ModularCurve.isLevelPStructure_cuspData
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.34379+00:00
-- url     : https://prove2.me/theorems/a5d57e9c-eabb-5062-a54b-b2fb45dea266
-- title:
--   Cusp points are level-p structures on the Tate curve
-- statement:
--   Let $R$ be a commutative ring and $p$ a prime with $5 \le p$ and $p$ invertible in $R$, and let $\zeta \in R^\times$ satisfy $\sum_{i<p} \zeta^i = 0$. Let $v, w \colon \mathrm{Fin}\,2 \to \mathbb{Z}/p$ be two vectors with $v_0 w_1 - v_1 w_0 \neq 0$ in $\mathbb{Z}/p$. Work over the Laurent series ring $R(\!(q)\!)$ with the Weierstrass curve [`ModularCurve.tateBase R p`](def/ModularCurve_TateSlots.html#L46), the Tate curve over $R(\!(q)\!)$ pulled back along the substitution $q \mapsto q^p$ (the ring map [`ModularCurve.qExpand`](def/ModularCurve_X0.html#L25)). To a vector $u$ the construction [`ModularCurve.cuspPoint`](def/ModularCurve_KatzLevelPCusps.html#L59) attaches the affine point $(x_u, y_u)$ of this curve given by the toric point with parameter $\zeta^{(u_0)}$ when $u_1 = 0$, and by the non-toric point with parameters $\zeta^{(u_0)}$ and the representative of $u_1$ in $\{0,\dots,p-1\}$ otherwise; [`ModularCurve.cuspData R p ζ v w`](def/ModularCurve_KatzLevelPCusps.html#L71) is the pair of such points $P$ for $v$ and $Q$ for $w$. The assertion is that this pair satisfies [`ModularCurve.IsLevelPStructure`](def/ModularCurve_KatzLevelP.html#L104), that is: $P$ and $Q$ satisfy the affine Weierstrass equation; the division polynomial $\mathrm{pre}\Psi_p$ vanishes at $x_P$ and at $x_Q$; and both products $\prod_{a=1}^{(p-1)/2}\bigl(x_Q\,\Psi^2_a(x_P) - \Phi_a(x_P)\bigr)$ and $\prod_{a=1}^{(p-1)/2}\bigl(x_P\,\Psi^2_a(x_Q) - \Phi_a(x_Q)\bigr)$ are units of $R(\!(q)\!)$.
--
--   This is the statement that the points $\zeta^{a}q^{b}$, $\zeta^{c}q^{d}$ with $ad - bc \neq 0$ on the Tate curve $\mathrm{Tate}(q^p)$ constitute a Drinfeld basis of level $p$, expressed in division-polynomial coordinates; it is the general-basis form of the cusp computation, covering all cusps of $X(p)$ rather than a single chosen one. It is used in the comparison of $q$-expansions of level-$p$ forms with forms of level $\Gamma_0$, via [`ModularCurve.KatzGamma0Form.exists_pullbackLevelP_eq_of_qTwist_qExpansion_eq_of_five_le`](thm.html#ModularCurve.KatzGamma0Form.exists_pullbackLevelP_eq_of_qTwist_qExpansion_eq_of_five_le).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_isLevelPStructure_cuspData.lean

import Mathlib
import Definitions.Def_ModularForm_KatzLevelOne
import Definitions.Def_ModularCurve_KatzLevelP
import Definitions.Def_ModularCurve_KatzLevelPCusps

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

theorem ModularCurve.isLevelPStructure_cuspData {R : Type u} [CommRing R] {p : ℕ} [Fact p.Prime]
    (hp5 : 5 ≤ p) (hp : IsUnit (p : R)) (ζ : Rˣ) (hζ : ∑ i ∈ Finset.range p, (ζ : R) ^ i = 0)
    (v w : Fin 2 → ZMod p) (hvw : v 0 * w 1 - v 1 * w 0 ≠ 0) :
    ModularCurve.IsLevelPStructure (ModularCurve.tateBase R p) p (ModularCurve.cuspData R p ζ v w) := by sorry
