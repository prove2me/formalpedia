-- Prove2me | Theorems.Thm_ModularCurve_ModularPolynomialData_exists_veluQuotient_j_eq_of_mem_roots_fibrePoly
-- name    : ModularCurve.ModularPolynomialData.exists_veluQuotient_j_eq_of_mem_roots_fibrePoly
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:42.499921+00:00
-- url     : https://prove2.me/theorems/5187d7ab-6a39-5897-928a-4ec7727807f8
-- title:
--   Every root of Φ_ℓ(j(W),Y) is a Vélu quotient j-invariant
-- statement:
--   Let $K$ be an algebraically closed field and $\ell$ a prime with $\ell \neq 2$ and $\ell \neq 0$ in $K$. Let `data` be a `ModularPolynomialData ℓ`, that is, a polynomial $\Phi \in (\mathbb{Z}[X])[Y]$ which is monic in $Y$, of $Y$-degree $\psi(\ell) = \sum_{d \mid \ell,\ d \text{ squarefree}} \ell/d$, and which vanishes when its coefficients are specialised by $X \mapsto j(q)$ and its main variable at $j(q^\ell)$, both as Laurent series over $\mathbb{Q}$. Let $W$ be an elliptic Weierstrass curve over $K$, and let $y \in K$ belong to the multiset of roots of the one-variable polynomial $\mathrm{fibrePoly}\,\Phi\,j(W)$ over $K$, obtained from $\Phi$ by mapping each coefficient in $\mathbb{Z}[X]$ to $K$ by reduction of the integer coefficients followed by evaluation at $j(W)$ (so in particular this polynomial is nonzero). Then there is an affine point $Q$ of $W$ of exact additive order $\ell$ such that the Weierstrass curve $W.\mathrm{veluQuotient}$ taken over the finite set of coordinate pairs of $kQ$ for $1 \le k \le \ell/2$ — the curve with the same $a_1,a_2,a_3$ as $W$, with $a_4$ replaced by $a_4 - 5t$ and $a_6$ by $a_6 - b_2 t - 7w$, where $t,w$ are the sums of Vélu's quantities over that set — has nonzero discriminant, and its $j$-invariant, formed using that nonvanishing, equals $y$.
--
--   This is the "every root comes from a cyclic $\ell$-isogeny" half of the modular equation in characteristic prime to $\ell$: the fibre of the level-$\ell$ modular polynomial over $j(W)$ has all its roots of the form $j(W/\langle Q \rangle)$ for $Q$ of order $\ell$, realised through Vélu's formulae. It is used to show that the roots of $\Phi_\ell(j,Y)$ at a supersingular $j$-invariant are again supersingular.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_ModularPolynomialData_exists_veluQuotient_j_eq_of_mem_roots_fibrePoly.lean

import Mathlib
import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_FibrePoly
import Definitions.Def_WeierstrassCurve_Velu
import Definitions.Def_WeierstrassCurve_OddOrderSummingSet

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Polynomial ModularCurve WeierstrassCurve WeierstrassCurve.Affine

theorem ModularCurve.ModularPolynomialData.exists_veluQuotient_j_eq_of_mem_roots_fibrePoly
    {K : Type*} [Field K] [IsAlgClosed K] [DecidableEq K]
    {ℓ : ℕ} [Fact ℓ.Prime] (hℓ2 : ℓ ≠ 2) (hℓK : (ℓ : K) ≠ 0)
    (data : ModularPolynomialData ℓ) (W : WeierstrassCurve K) [W.IsElliptic]
    {y : K} (hy : y ∈ (fibrePoly data.Φ W.j).roots) :
    ∃ Q : W.toAffine.Point, addOrderOf Q = ℓ ∧
      ∃ hΔ : (W.veluQuotient (W.oddOrderSummingSet Q (ℓ / 2))).Δ ≠ 0,
        @WeierstrassCurve.j K _ (W.veluQuotient (W.oddOrderSummingSet Q (ℓ / 2)))
          ⟨isUnit_iff_ne_zero.mpr hΔ⟩ = y := by sorry
