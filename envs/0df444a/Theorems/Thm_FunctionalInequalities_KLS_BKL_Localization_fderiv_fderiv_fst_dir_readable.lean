-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_BKL_Localization_fderiv_fderiv_fst_dir_readable
-- name    : FunctionalInequalities.KLS.BKL.Localization.fderiv_fderiv_fst_dir_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:14:06.354487+00:00
-- url     : https://prove2.me/theorems/a0e8f301-14c9-4b9b-85b4-3ddfdb159789
-- title:
--   Second Derivative Along a First-Factor Direction
-- statement:
--   This is a calculus identity for a function on a product space.
--
--   Let $E$ and $L$ be real normed spaces, with $E$ an inner-product space, and let $H:E\times L\to\mathbb R$ be twice continuously differentiable. For $p=(p_1,p_2)\in E\times L$ and $u\in E$, the second derivative of $H$ at $p$ in the product-space direction $(u,0)$, applied twice, equals the iterated second derivative of the restriction $y\mapsto H(y,p_2)$ in direction $u$:
--
--   $$D^2H(p)[(u,0),(u,0)]
--   = D^2\bigl(y\mapsto H(y,p_2)\bigr)(p_1)[u,u].$$
--
--   The result is a technical partial-derivative identity, useful when expressing product-space Hessians through derivatives in the first parameter.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.KLS.BKL.Localization`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem fderiv_fderiv_fst_dir (H : E × L → ℝ) (hH : ContDiff ℝ 2 H) (p : E × L) (u : E) :
--       fderiv ℝ (fderiv ℝ H) p (u, 0) (u, 0) =
--         bilinearIteratedFDerivTwo ℝ (fun y => H (y, p.2)) p.1 u u
--   ```
--
--   **Module navigation**
--
--   Module: [`KLS/BKL/Localization/LogLaplaceGenerator`](https://prove2.me/theorems/590f3074-6616-4d0a-abfd-f622c05acbcf).
--
--   Next: [`sum_bilin_inverseSqrt_eq`](https://prove2.me/theorems/7f385f3c-593c-495c-ae8d-54a94b5ade43).
--
--   [Source excerpt, lines 67–69](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/BKL/Localization/LogLaplaceGenerator.lean#L67-L69) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/BKL/Localization/LogLaplaceGenerator.lean#L65-L91 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.BKL.Localization.LogLaplaceGenerator`, declaration `FunctionalInequalities.KLS.BKL.Localization.fderiv_fderiv_fst_dir`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Localization_LogLaplaceGenerator

variable {E L : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup L] [NormedSpace ℝ L]

theorem FunctionalInequalities.KLS.BKL.Localization.fderiv_fderiv_fst_dir_readable (H : E × L → ℝ) (hH : ContDiff ℝ 2 H) (p : E × L) (u : E) :
    fderiv ℝ (fderiv ℝ H) p (u, 0) (u, 0) =
      bilinearIteratedFDerivTwo ℝ (fun y => H (y, p.2)) p.1 u u := by sorry
