-- Prove2me | Theorems.Thm_ModularCurve_mem_ssJSet_of_mem_roots_fibrePoly
-- name    : ModularCurve.mem_ssJSet_of_mem_roots_fibrePoly
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.624895+00:00
-- url     : https://prove2.me/theorems/f3dbb8aa-4388-50cf-85d7-b4ec6418eaed
-- title:
--   Roots of the level-ℓ modular equation preserve supersingularity
-- statement:
--   Let $\kappa$ be an algebraically closed field, let $q$ be a prime and suppose $\kappa$ has characteristic $q$; let $\ell$ be a prime with $\ell \neq q$. Let `data` be a packet `ModularPolynomialData ℓ`, that is, a polynomial $\Phi \in \mathbb{Z}[X][Y]$ which is monic, of degree $\psi(\ell) = \sum_{d \mid \ell,\ d \text{ squarefree}} \ell/d$ in $Y$, and satisfies $\Phi(j(\tau), j(\ell\tau)) = 0$ as an identity of Laurent series (the relation `eval_eq_zero` between `evalAtJ` and `jqN ℓ`). Let $j, y \in \kappa$. Assume $j \in$ `ssJSet q κ`, i.e. for every Weierstrass curve $W$ over $\kappa$ with invertible discriminant and $j(W) = j$, every point $P$ of the associated affine curve with $q \cdot P = 0$ is the point at infinity. Assume further that $y$ lies in the root multiset of `fibrePoly data.Φ j`, the polynomial in $\kappa[Y]$ obtained from $\Phi$ by mapping coefficients along $\mathbb{Z} \to \kappa$ and specialising $X \mapsto j$; in particular that polynomial is nonzero and $\Phi(j, y) = 0$. The conclusion is that $y$ likewise lies in `ssJSet q κ`: every elliptic Weierstrass curve over $\kappa$ with $j$-invariant $y$ has no nonzero point killed by $q$.
--
--   This is the classical statement that the $\ell+1$ curves $\ell$-isogenous to a supersingular elliptic curve in characteristic $q \neq \ell$ are again supersingular, i.e. that the Hecke correspondence attached to $\Phi_\ell$ on the $j$-line preserves the supersingular locus. It is used in the construction of the Hecke action on divisors supported on supersingular points, and is cited in the treatment of specialisations of the modular curve and of the supersingular places occurring in Hecke divisors.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_mem_ssJSet_of_mem_roots_fibrePoly.lean

import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_FibrePoly

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve Polynomial

theorem ModularCurve.mem_ssJSet_of_mem_roots_fibrePoly
    {κ : Type*} [Field κ] [IsAlgClosed κ] [DecidableEq κ]
    (q : ℕ) [Fact q.Prime] [CharP κ q] {ℓ : ℕ} [Fact ℓ.Prime] (hℓq : ℓ ≠ q)
    (data : ModularPolynomialData ℓ) {j y : κ}
    (hj : j ∈ ssJSet q κ) (hy : y ∈ (fibrePoly data.Φ j).roots) :
    y ∈ ssJSet q κ := by sorry
