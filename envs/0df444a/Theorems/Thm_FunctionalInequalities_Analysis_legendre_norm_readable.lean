-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_legendre_norm_readable
-- name    : FunctionalInequalities.Analysis.legendre_norm_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:04:54.040421+00:00
-- url     : https://prove2.me/theorems/7eb3b3f3-e05d-4ad0-a70e-b08de926b3ea
-- title:
--   Legendre Transform of the Norm
-- statement:
--   This computes the extended-real Legendre transform of the norm.
--
--   For every $y$ in a real inner-product space,
--
--   $$
--   \operatorname{Leg}\bigl(x\mapsto\|x\|\bigr)(y)
--   =
--   \begin{cases}
--   0,&\|y\|\leq1,\\
--   +\infty,&\|y\|>1.
--   \end{cases}
--   $$
--
--   The equality is in `EReal`. Thus the conjugate of the norm is the indicator of the closed unit ball, with value $0$ on the ball and $+\infty$ outside.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem legendre_norm (y : E) :
--       legendre (fun x : E => (‖x‖ : EReal)) y = if ‖y‖ ≤ 1 then 0 else ⊤
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/Convex/Legendre`](https://prove2.me/theorems/ccf34d51-1332-4642-a3a3-dacdd0cbab81).
--
--   Supporting theorems: [`legendre_ne_bot_iff`](https://prove2.me/theorems/9d709974-65b3-421f-a939-a9573b181df1).
--
--   Previous: [`legendre_eq_interior_sup`](https://prove2.me/theorems/fb27a67d-8a39-4dbc-904c-e8977c7bb3af).
--
--   [Source excerpt, lines 311–312](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Convex/Legendre.lean#L311-L312) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Convex/Legendre.lean#L310-L342 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Convex.Legendre`, declaration `FunctionalInequalities.Analysis.legendre_norm`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Convex_Legendre

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem FunctionalInequalities.Analysis.legendre_norm_readable (y : E) :
    legendre (fun x : E => (‖x‖ : EReal)) y = if ‖y‖ ≤ 1 then 0 else ⊤ := by sorry
