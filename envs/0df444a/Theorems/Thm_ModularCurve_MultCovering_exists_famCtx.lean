-- Prove2me | Theorems.Thm_ModularCurve_MultCovering_exists_famCtx
-- name    : ModularCurve.MultCovering.exists_famCtx
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.082448+00:00
-- url     : https://prove2.me/theorems/309c073d-e2d4-5ff3-9e0d-c4a33e8a5c79
-- title:
--   Existence of a good-family context at prime level p
-- statement:
--   Let $p$ be a prime with $p \ge 5$, let $r$ be a natural number, and let $s : \mathrm{Fin}\,r \to \overline{\mathbb Q}(X_0(1\cdot p))$ be a family in the base-changed modular function field `modularFunctionFieldBar (1 * p)` which is an embedding basis in the sense of `IsEmbBasis`: $s$ is linearly independent over $\overline{\mathbb Q}$ and its span is the Riemann–Roch space $\{f : \forall v,\ v(f) \le \exp(D(v))\}$ of the divisor $D = (\mathrm{embDegree}\,(1\cdot p))\cdot \overline{\infty}$ supported at the cusp at infinity. Then the type `FamCtx p r` is non-empty, i.e. there exists a family $t : \mathrm{Fin}\,r \to \overline{\mathbb Q}(X_0(1\cdot p))$ together with: a family $t^{\mathrm{Rat}}$ in `modularFunctionFieldFull (1 * p)` whose coefficientwise image under the embedding $\mathbb Q \to \overline{\mathbb Q}$ of Laurent series is $t$ (so $t$ is defined over $\mathbb Q$); the property that $t$ is again an embedding basis for the same divisor; $t_0 = 1$; and, for every valuation subring $A$ of $\overline{\mathbb Q}$ with $p$ a non-unit of $A$ and residue field of characteristic $p$, and every chart context $\Gamma : \mathrm{ChartCtx}\,p\,A$, two reduction conditions, summarised here: on the chart at infinity all $t_l$ are integral, $t_0$ reduces to $1$, and for $l \ge 1$ the reductions are $\mathrm{ssPolyBar}\,\Gamma$ times $P_l(\bar\jmath)$ for polynomials $P_l$ over the residue field forming a basis of the polynomials of degree $< \mathrm{mAnnuli}\,p$; and, provided every value $\mathrm{ssValue}\,\Gamma\,e$ differs from $0$ and $1728$, on the chart at zero the rescaled elements $p^{-\mathrm{hasseExp}}t_l$ are integral, their reductions multiplied by $\mathrm{ssPolyBarZero}\,\Gamma$ are $P_l(\bar\jmath)$ for a basis $(P_l)$ of the polynomials of degree $\le \mathrm{mAnnuli}\,p$ with $P_0 = \prod_e (X - (\mathrm{ssValue}\,\Gamma\,e)^p)$.
--
--   This is the existence step for the rational basis, normalised at both cusps, that underlies the construction of the uniform multiplicative covering of $X_0(p)$ for $p \ge 5$; the hypothesis that an embedding basis exists fixes $r$, which elsewhere is identified with $\mathrm{mAnnuli}\,p + 1$. It is used by [`ModularCurve.exists_uniform_multCovering_with_certifiedFamily_of_prime_of_five_le`](thm.html#ModularCurve.exists_uniform_multCovering_with_certifiedFamily_of_prime_of_five_le).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_MultCovering_exists_famCtx.lean

import Definitions.Def_ModularCurve_MultCoveringFamily

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.MultCovering

theorem ModularCurve.MultCovering.exists_famCtx (p : ℕ) [Fact p.Prime] (hp5 : 5 ≤ p) {r : ℕ}
    (s : Fin r → ↥(modularFunctionFieldBar (1 * p))) (hs : IsEmbBasis (1 * p) s) :
    Nonempty (ModularCurve.MultCovering.FamCtx p r) := by sorry
