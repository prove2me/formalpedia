-- Prove2me | Theorems.Thm_ModularCurve_ModularPolynomialData_hasRamBound_three_of_isRoot_at_zero_of_odd
-- name    : ModularCurve.ModularPolynomialData.hasRamBound_three_of_isRoot_at_zero_of_odd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:42.499921+00:00
-- url     : https://prove2.me/theorems/dbb0d3a2-2171-5545-9f0e-e7d76d439858
-- title:
--   Roots of Φ_N(t,Y) over ℚ̄ have ramification bound 3 (N odd)
-- statement:
--   Let $N$ be a natural number with $N \neq 0$ and $N$ odd, and let `data` be a piece of modular polynomial data of level $N$: a polynomial $\Phi \in \mathbb Z[X][Y]$ which is monic (in $Y$), whose degree equals $\sum_{d \mid N,\ d \text{ squarefree}} N/d$, and which satisfies $\Phi = 0$ after evaluating its $\mathbb Z[X]$-coefficients by `evalAtJ`, the ring homomorphism $\mathbb Z[X] \to \mathbb Q((q))$ sending $X$ to the $q$-expansion `jq` of $j$, at the element `jqN N` (the corresponding expansion at level $N$). Let $r$ be an element of the Hahn series field $\mathrm{HahnSeries}\ \mathbb Q\ \overline{\mathbb Q}$, with rational exponents and coefficients in `AlgebraicClosure ℚ`. Assume $r$ is a root of the one-variable polynomial obtained from $\Phi$ by mapping each coefficient through evaluation of $\mathbb Z[X]$ at the monomial $t =$ `HahnSeries.single 1 1`, along the canonical map $\mathbb Z \to \mathrm{HahnSeries}\ \mathbb Q\ \overline{\mathbb Q}$; that is, $\Phi(t, r) = 0$. The conclusion is [`HahnSeries.HasRamBound 3 r`](def/HahnSeries_RamificationBound.html#L32), i.e. the support of $r$ is contained in the range of $k \mapsto k/3$ for $k \in \mathbb Z$, so $r$ is a Puiseux series in $t^{1/3}$.
--
--   In classical terms: taking $t = j$ as a local parameter on the $j$-line at $j = 0$, the roots of $\Phi_N(t,Y)$ are the local branches of $X_0(N)$ above $j = 0$, and the assertion is that the ramification index of $X_0(N) \to X(1)$ at each such point divides $3$, reflecting the order-$3$ stabiliser of the elliptic point $\rho = e^{2\pi i/3}$ in $\mathrm{PSL}_2(\mathbb Z)$. It feeds the divisibility statements [`ModularCurve.ord_jBar_dvd_three_of_odd`](thm.html#ModularCurve.ord_jBar_dvd_three_of_odd), [`ModularCurve.ord_jBar_dvd_three_of_pos_of_forall_isRoot_hasRamBound`](thm.html#ModularCurve.ord_jBar_dvd_three_of_pos_of_forall_isRoot_hasRamBound) and [`ModularCurve.ord_jBar_sub_1728_dvd_two_of_odd`](thm.html#ModularCurve.ord_jBar_sub_1728_dvd_two_of_odd).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_ModularPolynomialData_hasRamBound_three_of_isRoot_at_zero_of_odd.lean

import Mathlib
import Definitions.Def_ModularCurve_X0
import Definitions.Def_HahnSeries_RamificationBound

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularCurve.ModularPolynomialData.hasRamBound_three_of_isRoot_at_zero_of_odd
    {N : ℕ} [NeZero N] (hN : Odd N) (data : ModularCurve.ModularPolynomialData N)
    (r : HahnSeries ℚ (AlgebraicClosure ℚ))
    (hroot : (data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom (HahnSeries ℚ (AlgebraicClosure ℚ)))
      (HahnSeries.single (1 : ℚ) (1 : AlgebraicClosure ℚ)))).IsRoot r) :
    HahnSeries.HasRamBound 3 r := by sorry
