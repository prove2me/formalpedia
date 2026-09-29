-- Prove2me | Theorems.Thm_ModularCurve_ModularPolynomialData_fibrePoly_j_eq_prod_veluQuotient_j
-- name    : ModularCurve.ModularPolynomialData.fibrePoly_j_eq_prod_veluQuotient_j
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:42.499921+00:00
-- url     : https://prove2.me/theorems/0340eced-3b26-5370-9dab-1d7d93d99660
-- title:
--   Modular equation of odd prime level via Vélu quotients
-- statement:
--   Let $K$ be an algebraically closed field and $\ell$ a prime with $\ell \neq 2$ and $\ell \neq 0$ in $K$. Let `data` be a `ModularPolynomialData` for $\ell$: a polynomial $\Phi \in \mathbb{Z}[X][Y]$ that is monic in $Y$, of degree in $Y$ equal to $\sum_{d \mid \ell,\ d \text{ squarefree}} \ell/d$, and that vanishes when $X$ is substituted by the $q$-expansion of $j$ and $Y$ by that of $j(q^{\ell})$ in Laurent series over $\mathbb{Q}$. Let $W$ be a Weierstrass curve over $K$ which is elliptic, let $\iota$ be a finite index type with $\ell+1$ elements, and let $Q : \iota \to W(K)$ be points on the associated affine curve, each of additive order exactly $\ell$, such that $i \mapsto \langle Q_i\rangle$ (the subgroup of integer multiples) is injective. Assume, for every $i$, that the discriminant $\Delta$ of the Vélu quotient $W/\langle Q_i\rangle$ is nonzero, where this quotient is the Weierstrass curve with the same $a_1,a_2,a_3$ and with $a_4$ replaced by $a_4 - 5\,t(S_i)$ and $a_6$ by $a_6 - b_2\,t(S_i) - 7\,w(S_i)$, the Vélu sums $t$ and $w$ being taken over the set $S_i$ of affine coordinate pairs of $kQ_i$ for $1 \le k \le \lfloor \ell/2 \rfloor$ (the point at infinity contributing $(0,0)$). Then, in $K[Y]$, the polynomial obtained from $\Phi$ by mapping its coefficient polynomials to $K$ through substitution of $j(W)$ equals $\prod_i \bigl(Y - j(W/\langle Q_i\rangle)\bigr)$, the $j$-invariants being formed using the nonvanishing of the discriminants.
--
--   This is the modular equation of odd prime level $\ell$ in any characteristic not dividing $\ell$: specialising the level-$\ell$ modular polynomial at $X = j(E)$ gives, with multiplicities, the product over the $\ell+1$ cyclic subgroups of order $\ell$ of $E$ of $Y - j(E/C)$. It underlies the identification of the roots of $\Phi_\ell(j(E),Y)$ with $j$-invariants of cyclic $\ell$-isogenous curves, and is used in the analysis of roots of the modular polynomial at places and in the resulting bijection onto cyclic quotient $j$-invariants.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_ModularPolynomialData_fibrePoly_j_eq_prod_veluQuotient_j.lean

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

theorem ModularCurve.ModularPolynomialData.fibrePoly_j_eq_prod_veluQuotient_j
    {K : Type*} [Field K] [IsAlgClosed K] [DecidableEq K]
    {ℓ : ℕ} [Fact ℓ.Prime] (hℓ2 : ℓ ≠ 2) (hℓK : (ℓ : K) ≠ 0)
    (data : ModularPolynomialData ℓ) (W : WeierstrassCurve K) [W.IsElliptic]
    {ι : Type*} [Fintype ι] (hι : Fintype.card ι = ℓ + 1)
    (Q : ι → W.toAffine.Point) (hQ : ∀ i, addOrderOf (Q i) = ℓ)
    (hQinj : Function.Injective fun i => AddSubgroup.zmultiples (Q i))
    (hΔ : ∀ i, (W.veluQuotient (W.oddOrderSummingSet (Q i) (ℓ / 2))).Δ ≠ 0) :
    fibrePoly data.Φ W.j =
      ∏ i, (X - C (@WeierstrassCurve.j K _
        (W.veluQuotient (W.oddOrderSummingSet (Q i) (ℓ / 2))) ⟨isUnit_iff_ne_zero.mpr (hΔ i)⟩)) := by sorry
