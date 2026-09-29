-- Prove2me | Theorems.Thm_ModularCurve_heckeDivFibreDescends_of_separable_phi_map
-- name    : ModularCurve.heckeDivFibreDescends_of_separable_phi_map
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.700479+00:00
-- url     : https://prove2.me/theorems/6a96c13a-82d9-5663-a0fc-5b0519a3df83
-- title:
--   Descent of the fibre Hecke correspondence to Pic⁰
-- statement:
--   Let $k$ be a field, let $N$ and $q$ be nonzero natural numbers with $q$ prime, and let `data` be a `ModularPolynomialData q`, that is a monic $\Phi \in \mathbb{Z}[X][Y]$ whose degree in $Y$ equals the Dedekind $\psi$-value $\psi(q) = \sum_{d \mid q,\ d \text{ squarefree}} q/d$ and which satisfies $\Phi(j(q), j_q) = 0$ in Laurent series over $\mathbb{Q}$ (evaluation of the coefficients at the $q$-expansion of $j$). Assume: `hsymm`, that $\Phi$ is symmetric in the sense that for all Laurent series $x, y$ over $\mathbb{Q}$ one has $\Phi.\mathrm{eval}_2(\mathrm{aeval}\ x)\ y = \Phi.\mathrm{eval}_2(\mathrm{aeval}\ y)\ x$; `hqk`, that $q \neq 0$ in $k$; and `hsep`, that the polynomial obtained from $\Phi$ by reducing its integer coefficients into $k$ and then viewing it as a polynomial in one variable over the rational function field $\mathrm{RatFunc}\ k$ is separable. The conclusion is `HeckeDivFibreDescends k N q`: for every witness that the roof field $\mathrm{charLDegeneracyRoof}\ k\ N\ q = k(j, j_N, j_q, j_{Nq}) \subseteq k((t))$ has principal divisors, and for all witnesses that the ring maps underlying `heckeBetaC k N q` and `heckeAlphaC k N q` are integral, the additive endomorphism `heckeDivFibre` of $\mathrm{Divisor}\ k\ (\mathrm{modularFunctionFieldC}\ k\ N)$, namely the divisor correspondence attached to this pair of legs, carries degree-zero divisors to degree-zero divisors and principal divisors to principal divisors.
--
--   This is the statement that the index-$q$ Hecke correspondence, realised at the level of divisors on the modular curve of level $N$ through the degeneracy roof $k(j, j_N, j_q, j_{Nq})$, is well defined on the degree-zero divisor class group, the degree part coming from the fundamental identity for a finite separable extension of function fields and the principal part from the norm formula for pushforward. It is the separability-hypothesis form of the result, and is used by [`ModularCurve.heckeInputsFibre_of_separable_phi_map`](thm.html#ModularCurve.heckeInputsFibre_of_separable_phi_map), [`ModularCurve.heckeInputsFibre_of_natCast_ne_zero`](thm.html#ModularCurve.heckeInputsFibre_of_natCast_ne_zero) and [`ModularCurve.heckeInputsFibre_of_prime`](thm.html#ModularCurve.heckeInputsFibre_of_prime) to assemble the data defining Hecke operators on $\mathrm{Pic}^0$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_heckeDivFibreDescends_of_separable_phi_map.lean

import Definitions.Def_ModularCurve_CharLDegeneracyHecke
import Definitions.Def_ModularCurve_PhiGen

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ModularCurve.heckeDivFibreDescends_of_separable_phi_map (k : Type*) [Field k]
    (N q : ℕ) [NeZero N] [NeZero q] [Fact q.Prime]
    (data : ModularCurve.ModularPolynomialData q) (hsymm : ModularCurve.EvalSymm data.Φ)
    (hqk : (q : k) ≠ 0)
    (hsep : ((data.Φ.map (Polynomial.mapRingHom (Int.castRingHom k))).map
      (algebraMap (Polynomial k) (RatFunc k))).Separable) :
    ModularCurve.HeckeDivFibreDescends k N q := by sorry
