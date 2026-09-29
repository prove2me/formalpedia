-- Prove2me | Theorems.Thm_ModularCurve_inLine_cuspData_smul_of_five_le
-- name    : ModularCurve.inLine_cuspData_smul_of_five_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.700479+00:00
-- url     : https://prove2.me/theorems/c338560d-5111-5ade-95be-4b966cef6f5f
-- title:
--   Non-toric cusp points: x(t· w) on the line of x(w)
-- statement:
--   Let $R$ be a commutative ring, $p$ a prime with $5 \le p$, and suppose that the image of $p$ in $R$ is a unit. Let $\zeta \in R^{\times}$ satisfy $\sum_{i<p} \zeta^{i} = 0$, and let $v, v', w \colon \mathrm{Fin}\,2 \to \mathbb{Z}/p$ be pairs of residues with $w\,1 \neq 0$, and $t \in \mathbb{Z}/p$ with $t \neq 0$. The curve in play is [`ModularCurve.tateBase R p`](def/ModularCurve_TateSlots.html#L46), the Weierstrass curve over the Laurent series $R((q))$ obtained from the Tate curve with universal integral coefficients by the ring map $q \mapsto q^{p}$, i.e. $\mathrm{Tate}(q^{p})$. For a pair $u$ the quantity `(cuspData R p ζ v u).xQ` is the first coordinate of `cuspPoint R p ζ u`, namely $\mathrm{tateToricPoint}$ at $\zeta^{(u\,0).\mathrm{val}}$ if $u\,1 = 0$ and otherwise $\mathrm{nonToricPoint}$ at $\zeta^{(u\,0).\mathrm{val}}$ with exponent $(u\,1).\mathrm{val}$; it does not depend on the first entry of the data, so the choices $v$, $v'$ are immaterial. The conclusion is [`ModularCurve.InLine`](def/ModularCurve_KatzLevelP.html#L21) for these two $x$-coordinates: there exists a natural number $a$ with $1 \le a \le (p-1)/2$ (natural subtraction and division) such that, writing $x_0$ for the $x$-coordinate attached to $w$ and $x$ for that attached to $t \cdot w$, one has $x \cdot \Psi_a^{2}(x_0) = \Phi_a(x_0)$ in $R((q))$, where $\Psi_a^2$ and $\Phi_a$ are the division polynomials of $\mathrm{Tate}(q^{p})$ in the variable $x$ alone.
--
--   This is the multiplication-by-$a$ relation $x([a]P) = \Phi_a(x_P)/\Psi_a^{2}(x_P)$, in cleared-denominator form, for the non-toric $p$-torsion points $\zeta^{w_0} q^{w_1}$ of the Tate curve $\mathrm{Tate}(q^{p})$ over $R((q))$, with $a$ the representative of $\pm t$ in $[1,(p-1)/2]$. It is the shape consumed by [`ModularCurve.KatzGamma0Form.exists_pullbackLevelP_eq_of_qTwist_qExpansion_eq_of_five_le`](thm.html#ModularCurve.KatzGamma0Form.exists_pullbackLevelP_eq_of_qTwist_qExpansion_eq_of_five_le) in the analysis of $q$-expansions at the cusps of the level-$p$ moduli problem.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_inLine_cuspData_smul_of_five_le.lean

import Mathlib
import Definitions.Def_ModularForm_KatzLevelOne
import Definitions.Def_ModularCurve_KatzLevelP
import Definitions.Def_ModularCurve_KatzLevelPCusps

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

theorem ModularCurve.inLine_cuspData_smul_of_five_le {R : Type u} [CommRing R] {p : ℕ} [Fact p.Prime]
    (hp5 : 5 ≤ p) (hp : IsUnit (p : R)) (ζ : Rˣ) (hζ : ∑ i ∈ Finset.range p, (ζ : R) ^ i = 0)
    (v v' w : Fin 2 → ZMod p) (hw : w 1 ≠ 0) (t : ZMod p) (ht : t ≠ 0) :
    ModularCurve.InLine (ModularCurve.tateBase R p) p (ModularCurve.cuspData R p ζ v w).xQ
      (ModularCurve.cuspData R p ζ v' (t • w)).xQ := by sorry
