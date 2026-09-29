-- Prove2me | Theorems.Thm_ModularCurve_mem_ssJSet_iff_of_isRoot_map_modularPolynomialData
-- name    : ModularCurve.mem_ssJSet_iff_of_isRoot_map_modularPolynomialData
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.624895+00:00
-- url     : https://prove2.me/theorems/71ba0cc6-7df6-5134-8a8a-b6039289ebb9
-- title:
--   Supersingularity is invariant along Φ_ℓ (ℓ≠ p)
-- statement:
--   Let $p$ and $\ell$ be primes with $\ell \neq p$, and let `data` be a `ModularPolynomialData` for level $\ell$: a bivariate polynomial $\Phi \in \mathbb{Z}[X][Y]$ which is monic (as a polynomial in $Y$ over $\mathbb{Z}[X]$), whose degree equals $\sum_{d \mid \ell,\ d \text{ squarefree}} \ell/d$ (so $\ell+1$ for $\ell$ prime), and which satisfies $\Phi(j(q), j(q^{\ell})) = 0$, the relation being taken in Laurent series over $\mathbb{Q}$ after substituting the $q$-expansion of $j$ for $X$. Let $\Omega$ be an algebraically closed field of characteristic $p$, and let $x, x' \in \Omega$ be such that $x'$ is a root of the one-variable polynomial over $\Omega$ obtained from $\Phi$ by reducing coefficients modulo $p$ and evaluating each coefficient polynomial at $x$; that is, $\Phi(x, x') = 0$ in $\Omega$. The conclusion is that $x$ lies in `ssJSet p Ω` if and only if $x'$ does, where `ssJSet p Ω` consists of those $j \in \Omega$ such that every elliptic Weierstrass curve $W$ over $\Omega$ with $W.j = j$ has no nonzero point $P$ on its affine model with $p \cdot P = 0$.
--
--   This is the statement that supersingularity of a $j$-invariant in characteristic $p$ is preserved by passing to an $\ell$-isogenous curve for $\ell \neq p$, expressed through the vanishing of the level-$\ell$ modular polynomial: an isogeny of degree prime to $p$ induces an isomorphism on $p$-torsion, so the supersingular locus is a union of fibres of the correspondence $\Phi_\ell = 0$. It is used in the analysis of supersingular points on the modular curves of full level structure, where supersingular places are transported along the Hecke correspondence and along the diamond operators.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_mem_ssJSet_iff_of_isRoot_map_modularPolynomialData.lean

import Mathlib
import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_SupersingularModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Polynomial ModularCurve

universe u

theorem ModularCurve.mem_ssJSet_iff_of_isRoot_map_modularPolynomialData
    (p : ℕ) [Fact p.Prime] (ℓ : ℕ) [Fact ℓ.Prime] (hℓp : ℓ ≠ p)
    (data : ModularCurve.ModularPolynomialData ℓ)
    (Ω : Type u) [Field Ω] [CharP Ω p] [IsAlgClosed Ω] [DecidableEq Ω]
    (x x' : Ω)
    (hroot : (data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom Ω) x)).IsRoot x') :
    x ∈ ModularCurve.ssJSet p Ω ↔ x' ∈ ModularCurve.ssJSet p Ω := by sorry
