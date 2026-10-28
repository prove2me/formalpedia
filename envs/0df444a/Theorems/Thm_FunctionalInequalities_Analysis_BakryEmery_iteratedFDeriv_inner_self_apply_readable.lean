-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_BakryEmery_iteratedFDeriv_inner_self_apply_readable
-- name    : FunctionalInequalities.Analysis.BakryEmery.iteratedFDeriv_inner_self_apply_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:02:20.535928+00:00
-- url     : https://prove2.me/theorems/93b102a6-8056-49d9-b513-0807baf24636
-- title:
--   Higher Leibniz Rule for an Inner Product Quadratic Form
-- statement:
--   This is the higher-order Leibniz rule for the map $w\mapsto\langle w,G(w)\rangle$.
--
--   Let $E$ be a real inner-product space, let $G:E\to E$ be $C^\infty$, let $d\in\mathbb N$, let $z\in E$, and let $h:\operatorname{Fin}(d+1)\to E$. Then
--
--   $$D^{d+1}\bigl(w\mapsto\langle w,G(w)\rangle\bigr)(z)[h]
--   =\left\langle z,D^{d+1}G(z)[h]\right\rangle
--   +\sum_{k=0}^{d}\left\langle h_k,D^dG(z)[h\text{ with }h_k\text{ removed}]\right\rangle.$$
--
--   The formula is a reusable pointwise identity for differentiating quadratic forms whose first factor is the identity map.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis.BakryEmery`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem iteratedFDeriv_inner_self_apply {G : E → E} (hG : ContDiff ℝ ∞ G) (d : ℕ) (z : E)
--       (h : Fin (d + 1) → E) :
--       iteratedFDeriv ℝ (d + 1) (fun w => ⟪w, G w⟫) z h =
--         ⟪z, iteratedFDeriv ℝ (d + 1) G z h⟫ +
--           ∑ k : Fin (d + 1), ⟪h k, iteratedFDeriv ℝ d G z (k.removeNth h)⟫
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/BakryEmery/IteratedDerivative`](https://prove2.me/theorems/ec55966f-66a5-4e3f-9fc7-b3e724ac29c7).
--
--   Next: [`iteratedFDeriv_succ_comp_perm_of_fix_zero`](https://prove2.me/theorems/cc6ef6bd-ffe5-427d-b172-1c1aebc1558a).
--
--   [Source excerpt, lines 45–49](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/BakryEmery/IteratedDerivative.lean#L45-L49) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/BakryEmery/IteratedDerivative.lean#L43-L118 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.BakryEmery.IteratedDerivative`, declaration `FunctionalInequalities.Analysis.BakryEmery.iteratedFDeriv_inner_self_apply`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_IteratedDerivative

open scoped RealInnerProductSpace ContDiff
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem FunctionalInequalities.Analysis.BakryEmery.iteratedFDeriv_inner_self_apply_readable {G : E → E} (hG : ContDiff ℝ ∞ G) (d : ℕ) (z : E)
    (h : Fin (d + 1) → E) :
    iteratedFDeriv ℝ (d + 1) (fun w => ⟪w, G w⟫) z h =
      ⟪z, iteratedFDeriv ℝ (d + 1) G z h⟫ +
        ∑ k : Fin (d + 1), ⟪h k, iteratedFDeriv ℝ d G z (k.removeNth h)⟫ := by sorry
