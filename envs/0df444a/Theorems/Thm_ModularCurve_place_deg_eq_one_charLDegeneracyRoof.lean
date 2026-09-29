-- Prove2me | Theorems.Thm_ModularCurve_place_deg_eq_one_charLDegeneracyRoof
-- name    : ModularCurve.place_deg_eq_one_charLDegeneracyRoof
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.985053+00:00
-- url     : https://prove2.me/theorems/903e6525-7670-5af0-b72a-f0ce89ca84d2
-- title:
--   Places of the characteristic-ℓ degeneracy roof have degree one
-- statement:
--   Let $k$ be an algebraically closed field and let $N$ and $q$ be nonzero natural numbers. Write $\tilde j =$ `jqModC k` for the element of the Laurent series field $k((q))$ given by $q^{-1}$ times the image of the integral power series `jNum` under $\mathbb{Z} \to k$, and for $M \ge 1$ let `jqNModC k M` be the series obtained from $\tilde j$ by the substitution $q \mapsto q^{M}$. The field `charLDegeneracyRoof k N q` is the intermediate field of $k((q))/k$ generated over $k$ by the four elements `jqModC k`, `jqNModC k N`, `jqNModC k q` and `jqNModC k (N * q)`. The assertion is that for every place $W$ of this field over $k$ — that is, every valuation subring of it which contains the image of $k$, is not the whole field, and is a principal ideal ring — the degree of $W$, defined as the $k$-dimension of the residue field of that valuation subring, equals $1$. No hypothesis on the characteristic of $k$ is imposed, despite the name.
--
--   This is the statement that all places of the four-generator degeneracy roof $k(\tilde j,\tilde j_N,\tilde j_q,\tilde j_{Nq})$ are rational when the constant field is algebraically closed. It discharges the degree hypothesis in the computation of the inertia degrees along the two degeneracy maps, and is used by [`ModularCurve.inertiaDegAlong_heckeAlphaC_eq_one`](thm.html#ModularCurve.inertiaDegAlong_heckeAlphaC_eq_one), [`ModularCurve.inertiaDegAlong_heckeBetaC_eq_one`](thm.html#ModularCurve.inertiaDegAlong_heckeBetaC_eq_one) and [`ModularCurve.reductionModL_heckeOperatorBar_of_ne`](thm.html#ModularCurve.reductionModL_heckeOperatorBar_of_ne).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_place_deg_eq_one_charLDegeneracyRoof.lean

import Definitions.Def_ModularCurve_CharLDegeneracyHecke

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve AlgebraicCurve
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

theorem ModularCurve.place_deg_eq_one_charLDegeneracyRoof
    (k : Type*) [Field k] [IsAlgClosed k] (N q : ℕ) [NeZero N] [NeZero q]
    (W : AlgebraicCurve.Place k (charLDegeneracyRoof k N q)) :
    W.deg = 1 := by sorry
