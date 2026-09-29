-- Prove2me | Theorems.Thm_ModularCurve_thetaL_jqNModC_ne_zero
-- name    : ModularCurve.thetaL_jqNModC_ne_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:54.908972+00:00
-- url     : https://prove2.me/theorems/e6e5ae34-e1d0-5f60-93e9-73138eb6b0ac
-- title:
--   Non-vanishing of θ(j(q^N))
-- statement:
--   Let $K$ be a field, let $N$ be a nonzero natural number, and assume that the image of $N$ in $K$ is nonzero. Consider the Laurent series $j(q) = q^{-1} \cdot \iota(\mathtt{jNum})$ over $K$, where $\iota(\mathtt{jNum})$ denotes the power series with integer coefficients `jNum` pushed forward along the ring homomorphism $\mathbb{Z} \to K$ and regarded as a Laurent series, and $q^{-1}$ is the Hahn series `single (-1) 1`; this is [`ModularCurve.jqModC K`](def/ModularCurve_JqCoeff.html#L15). Let [`ModularCurve.jqNModC K N`](def/ModularCurve_JqCoeff.html#L18) be its image under the ring homomorphism [`ModularCurve.qExpand K N`](def/ModularCurve_X0.html#L25), which rescales the exponent group by multiplication by $N$ on $\mathbb{Z}$, i.e. performs the substitution $q \mapsto q^N$. Let [`ModularCurve.thetaL K`](def/ModularCurve_QExpansionDiff.html#L16) be the $K$-linear operator on Laurent series over $K$ sending $f$ to `single 1 1` times the formal derivative of $f$, that is $\theta = q\,\mathrm{d}/\mathrm{d}q$. The assertion is that $\theta\bigl(j(q^N)\bigr) \neq 0$ in the Laurent series field over $K$.
--
--   The point is that $j(q^N)$ has leading term $q^{-N}$, so $\theta(j(q^N))$ has coefficient $-N$ at $q^{-N}$, which is nonzero in $K$ by hypothesis; no characteristic assumption beyond $N \neq 0$ in $K$ is needed. It serves as the basic non-degeneracy input for later arguments on $q$-expansions, being used in the computations of leading terms and orders of vanishing attached to the supersingular places and Hecke multipliers, and in a criterion for membership in spaces of mod $p$ forms.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_thetaL_jqNModC_ne_zero.lean

import Definitions.Def_ModularCurve_QExpansionDiff
import Definitions.Def_ModularCurve_JqCoeff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularCurve.thetaL_jqNModC_ne_zero (K : Type*) [Field K] (N : ℕ) [NeZero N] (hN : (N : K) ≠ 0) :
    ModularCurve.thetaL K (ModularCurve.jqNModC K N) ≠ 0 := by sorry
