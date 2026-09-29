-- Prove2me | Theorems.Thm_ModularCurve_JZero_secProd_one_linSec_eq_eval_chowForm
-- name    : ModularCurve.JZero.secProd_one_linSec_eq_eval_chowForm
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:41.339792+00:00
-- url     : https://prove2.me/theorems/d4385b18-4826-5a90-b98e-1228d16c2a47
-- title:
--   Pivot value of a linear section equals the Chow form at e
-- statement:
--   Fix $N\ge 1$ and write $\bar F_N$ for `modularFunctionFieldBar N`, the subfield of $\mathrm{LaurentSeries}(\overline{\mathbb Q})$ obtained by base change to $\overline{\mathbb Q}$ of the modular function field of level $N$; places are valuation subrings of $\bar F_N$ containing $\overline{\mathbb Q}$, proper, with principal ideals, and a divisor is a finitely supported $\mathbb Z$-valued function on them. Let $r\in\mathbb N$ and let $s\colon \mathrm{Fin}\,r\to\bar F_N$ satisfy `IsEmbBasis N s`, i.e. $s$ is linearly independent over $\overline{\mathbb Q}$ and its $\overline{\mathbb Q}$-span is the Riemann–Roch space $\{f:\ v(f)\le \exp(D\,v)\ \text{for all places } v\}$ of the embedding divisor $D=(\mathrm{embDegree}\,N)\cdot[\text{the cusp } \infty]$. Let $e\colon \mathrm{Fin}\,r\to\overline{\mathbb Q}$ and let $Z$ be an arbitrary divisor. Then $$\prod_{w}\Big(\big(\textstyle\sum_i e_i s_i\big)\cdot s_{\mathrm{piv}(w)}^{-1}\Big)(w)^{\,\max(Z_w,0)}\;=\;\prod_{w}\Big(\textstyle\sum_i e_i\,\big(s_i s_{\mathrm{piv}(w)}^{-1}\big)(w)\Big)^{\,\max(Z_w,0)},$$ the left side being `secProd s 1 (linSec s e) Z` and the right side the evaluation at $e$ of the Chow form `chowForm s Z`; here $(\cdot)(w)$ is residue evaluation at $w$, $\mathrm{piv}(w)$ is the pivot index of $s$ at $w$, and both sides truncate multiplicities by `Int.toNat`, so no effectivity hypothesis on $Z$ is required.
--
--   This is the compatibility, for zero-cycles on the modular curve, between a linear section of the embedding system $s$ evaluated in the degree-one pivot trivialisation at each point of the cycle and the Chow form of the cycle evaluated at the coefficient vector $e$. It is what lets identities for hyperplane sections be read as identities of Chow forms, and it is used in the cocycle identity [`ModularCurve.JZero.hyperplaneSection_cocycle`](thm.html#ModularCurve.JZero.hyperplaneSection_cocycle) for the hyperplane-section defect.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JZero_secProd_one_linSec_eq_eval_chowForm.lean

import Definitions.Def_ModularCurve_JZeroHeightForm
import Definitions.Def_AlgebraicCurve_ChordalProximity
import Definitions.Def_AlgebraicCurve_CycleChowForm

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

open AlgebraicCurve ModularCurve

theorem ModularCurve.JZero.secProd_one_linSec_eq_eval_chowForm (N : ℕ) [NeZero N] {r : ℕ}
    (s : Fin r → modularFunctionFieldBar N) (hs : IsEmbBasis N s)
    (e : Fin r → AlgebraicClosure ℚ) (Z : Divisor (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) :
    secProd s 1 (linSec s e) Z = MvPolynomial.eval e (chowForm s Z) := by sorry
