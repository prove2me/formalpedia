-- Prove2me | Theorems.Thm_HLambdaG_Main_lemma_2
-- name    : HLambdaG.Main.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T08:44:28.5425+00:00
-- url     : https://prove2.me/theorems/5a612956-46d8-4862-b4f1-ede92495520a
-- title:
--   Lemma 2, p. 638 — composition bounds for the inverse time change
-- statement:
--   Let $T$ be a finite, nonnegative, nondecreasing, right-continuous time change on $[0,\infty)$ with $T(s)\to\infty$, and let $S(t)=\inf\{s\geq0:T(s)>t\}$. For every $t\geq0$,
--
--   $$
--   T(S(t))\geq t\geq T(S(t)-).
--   $$
--
--   These inequalities locate a time $t$ between the value and left limit of its inverse image, including at jumps of $T$.
--
--   **Formalization Note** The left limit is $\sup_{0\leq u<S(t)}T(u)$; in particular, $T(0-)=0$ when $S(t)=0$. This endpoint convention is needed for the stated inequality at $t=0$.
-- source:
--   Glynn and Whitt, Extensions of the queueing relations L = λW and H = λG, Oper. Res. 37 (1989), p. 638, Lemma 2, https://doi.org/10.1287/opre.37.4.634

import Mathlib
import Definitions.Def_HLambdaG_Main_Setting

open scoped NNReal

namespace HLambdaG.Main

/-- Lemma 2, p. 638: composition inequalities for the right-continuous inverse. -/
theorem lemma_2 (τ : TimeChange) (t : ℝ≥0) :
    t ≤ τ.T (inv τ t) ∧ leftLim τ (inv τ t) ≤ t := by sorry

end HLambdaG.Main
