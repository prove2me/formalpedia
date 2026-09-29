-- Prove2me | Theorems.Thm_ModularCurve_CupPairing_mult_mul_pair_eq_neg_finsum
-- name    : ModularCurve.CupPairing.mult_mul_pair_eq_neg_finsum
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:13.065378+00:00
-- url     : https://prove2.me/theorems/538cc141-3cee-5f15-b559-eec0f24f80d3
-- title:
--   Cup pairing of parabolic characters as a quotient sum
-- statement:
--   Let $\Gamma\le \mathrm{SL}_2(\mathbb Z)$ be a subgroup of finite index, and let $x,y\colon \mathrm{Additive}\,\Gamma\to\mathbb Z$ be additive homomorphisms that are parabolic in the sense of [`ModularCurve.Period.IsParabolicHom`](def/ModularCurve_PeriodMap.html#L15), i.e. $x$ (resp. $y$) vanishes on every $\gamma\in\Gamma$ whose integral matrix satisfies $(\mathrm{tr}\,\gamma)^2=4$. Suppose given $F\colon \mathrm{SL}_2(\mathbb Z)\to\mathbb Z$ with $F(Tg)=F(g)$, $F(-g)=F(g)$ and $F(g\gamma)=F(g)+x(\gamma)$ for all $g$ and all $\gamma\in\Gamma$, and $a,b\colon \mathrm{SL}_2(\mathbb Z)\to\mathbb Z$ with $a(Sg)=a(g)$, $b(STg)=b(g)$ and $a(g\gamma)=a(g)+y(\gamma)$, $b(g\gamma)=b(g)+y(\gamma)$, where $S,T$ are `ModularGroup.S`, `ModularGroup.T`. Suppose further that $\Phi\colon \mathrm{SL}_2(\mathbb Z)/\Gamma\to\mathbb Z$ satisfies $\Phi(g\Gamma)=(F(g)-F(Sg))\,(b(g)-a(g))$ for every $g$. The conclusion is the identity in $\mathbb Q$
--   $$m_\Gamma\cdot \mathrm{pair}\,\Gamma\,(x_{\mathbb Q})\,(y_{\mathbb Q}) \;=\; -\sum\nolimits^{\mathrm f}_{q}\Phi(q),$$
--   where $x_{\mathbb Q},y_{\mathbb Q}$ are $x,y$ followed by the cast $\mathbb Z\to\mathbb Q$, $m_\Gamma=$ [`ModularCurve.CupPairing.mult`](def/ModularCurve_CupPairing.html#L14) $\Gamma$ is $1$ if $-1\in\Gamma$ and $2$ otherwise, the right-hand side is the finite sum of $\Phi$ over $\mathrm{SL}_2(\mathbb Z)/\Gamma$, cast to $\mathbb Q$, and $\mathrm{pair}\,\Gamma\,\varphi\,\psi$ is, for $\Gamma$ of finite index, the quantity $\mathrm{cuspSum}\,\Gamma\,h/(2m_\Gamma)$ for a chosen $h\colon\Gamma\to\mathbb Q$ with $h(gg')=h(g)+h(g')-\omega_{\varphi,\psi}(g,g')$ for all $g,g'\in\Gamma$ (and $0$ if no such $h$ exists), $\omega$ being [`ModularCurve.PDPairing.omega`](def/ModularCurve_PDPairing.html#L386) and $\mathrm{cuspSum}$ the sum of $h$ over the chosen cusp generators.
--
--   This is the comparison between the cusp-residue description of the cup product of two parabolic characters of a finite-index subgroup of $\mathrm{SL}_2(\mathbb Z)$ and the cellular formula for that pairing on the complex attached to $\mathrm{SL}_2(\mathbb Z)/\Gamma$, in which the jump $F(g)-F(Sg)$ of a primitive of $x$ along an edge is paired with the difference $b(g)-a(g)$ of two potentials of $y$ coming from the tree of $\mathrm{SL}_2(\mathbb Z)$. It feeds the construction of a perfect pairing whose integral values recover [`ModularCurve.CupPairing.pair`](def/ModularCurve_CupPairing.html#L18), used in [`ModularCurve.CupPairing.exists_perfectPairing_intCast_eq_pair`](thm.html#ModularCurve.CupPairing.exists_perfectPairing_intCast_eq_pair).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_CupPairing_mult_mul_pair_eq_neg_finsum.lean

import Mathlib
import Definitions.Def_ModularCurve_CupPairing

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped MatrixGroups

theorem ModularCurve.CupPairing.mult_mul_pair_eq_neg_finsum (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex]
    (x y : Additive Γ →+ ℤ) (hx : ModularCurve.Period.IsParabolicHom Γ x)
    (hy : ModularCurve.Period.IsParabolicHom Γ y)
    (F : SL(2, ℤ) → ℤ) (hFT : ∀ g, F (ModularGroup.T * g) = F g) (hFneg : ∀ g, F (-g) = F g)
    (hFx : ∀ (g : SL(2, ℤ)) (γ : Γ), F (g * γ) = F g + x (Additive.ofMul γ))
    (a b : SL(2, ℤ) → ℤ) (ha : ∀ g, a (ModularGroup.S * g) = a g)
    (hb : ∀ g, b (ModularGroup.S * ModularGroup.T * g) = b g)
    (hay : ∀ (g : SL(2, ℤ)) (γ : Γ), a (g * γ) = a g + y (Additive.ofMul γ))
    (hby : ∀ (g : SL(2, ℤ)) (γ : Γ), b (g * γ) = b g + y (Additive.ofMul γ))
    (Φ : SL(2, ℤ) ⧸ Γ → ℤ)
    (hΦ : ∀ g, Φ (QuotientGroup.mk g) = (F g - F (ModularGroup.S * g)) * (b g - a g)) :
    (ModularCurve.CupPairing.mult Γ : ℚ) *
        ModularCurve.CupPairing.pair Γ ((Int.castAddHom ℚ).comp x) ((Int.castAddHom ℚ).comp y) =
      -((∑ᶠ q, Φ q : ℤ) : ℚ) := by sorry
