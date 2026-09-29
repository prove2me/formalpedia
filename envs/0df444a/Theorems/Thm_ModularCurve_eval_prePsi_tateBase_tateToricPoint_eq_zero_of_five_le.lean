-- Prove2me | Theorems.Thm_ModularCurve_eval_prePsi_tateBase_tateToricPoint_eq_zero_of_five_le
-- name    : ModularCurve.eval_prePsi_tateBase_tateToricPoint_eq_zero_of_five_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.209688+00:00
-- url     : https://prove2.me/theorems/0dbaa8bf-e6ab-5c02-b0d6-8992e0f1c21f
-- title:
--   Toric p-torsion points kill preΨₚ on Tate(qᵖ)
-- statement:
--   Let $K$ be a commutative ring and $p$ a prime with $5 \le p$, and let $c \in K^\times$ satisfy $c^p = 1$ and be such that $1 - c$ is a unit of $K$. Consider the Weierstrass curve [`ModularCurve.tateBase K p`](def/ModularCurve_TateSlots.html#L46) over the Laurent series ring $K((q))$: it is the Tate Weierstrass model `tatePowerSeries` over $K$, viewed over $K((q))$, with its coefficients pushed forward along the ring endomorphism `qExpand` of $K((q))$ that multiplies all exponents by $p$, i.e. the Tate curve with parameter $q^p$. Let $\mathrm{tateToricPoint}\,K\,p\,c$ be the pair of Laurent series whose first entry is the power series with constant coefficient $c\,(1-c)^{-2}$ and with $m$-th coefficient, for $m \ne 0$, equal to $\sum_{d \mid m,\ p \mid d} (m/d)\,(c^{m/d} + c^{-m/d}) - 2\,[\,p \mid m\,]\sum_{e \mid m/p} e$, and whose second entry is the analogous series built from the binomial coefficients $\binom{m/d}{2}$ and $\binom{m/d+1}{2}$; this is the abscissa–ordinate pair of the toric point with parameter $u = c$. The conclusion is that Mathlib's univariate division polynomial `preΨ` of `tateBase K p` at the integer $p$, evaluated at the first entry of this pair, is $0$ in $K((q))$.
--
--   This is the statement that the toric points $u = c$ with $c^p = 1$ of the Tate curve $\mathrm{Tate}(q^p)$ lie in the $p$-torsion, expressed by the vanishing of the $p$-division polynomial at their abscissa (for odd $p$, `preΨ` at $p$ is $\psi_p$). It is used to exhibit a level-$p$ structure on `tateBase` at Mazur's cusp and in the accompanying statements about the cusp point and the associated independence element.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_eval_prePsi_tateBase_tateToricPoint_eq_zero_of_five_le.lean

import Mathlib
import Definitions.Def_ModularCurve_TateSlots
import Definitions.Def_ModularCurve_KatzLevelPCusps

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

theorem ModularCurve.eval_prePsi_tateBase_tateToricPoint_eq_zero_of_five_le
    (K : Type u) [CommRing K] (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) (c : Kˣ) (hc : c ^ p = 1)
    (h1c : IsUnit (1 - (c : K))) :
    ((ModularCurve.tateBase K p).preΨ (p : ℤ)).eval (ModularCurve.tateToricPoint K p c).1 = 0 := by sorry
