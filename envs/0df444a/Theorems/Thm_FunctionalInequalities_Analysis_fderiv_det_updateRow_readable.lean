-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_fderiv_det_updateRow_readable
-- name    : FunctionalInequalities.Analysis.fderiv_det_updateRow_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:03:29.170757+00:00
-- url     : https://prove2.me/theorems/67074ad1-cbd5-49f9-85c5-5090bdb537d6
-- title:
--   Derivative of a Determinant with One Updated Row
-- statement:
--   This lemma is a technical determinant differentiation formula.
--
--   Let $E$ be a real normed vector space, let $A:E\to\operatorname{Fin}(n)\to\operatorname{Fin}(n)\to\mathbb R$, and suppose every scalar entry $y\mapsto A(y)_{kl}$ is differentiable at $x\in E$. Fix a row $j$, a replacement row $c:\operatorname{Fin}(n)\to\mathbb R$, and a direction $v\in E$. Then
--
--   $$D\left[y\mapsto\det(\operatorname{updateRow}(A(y),j,c))\right]_x(v)
--   =\sum_k \begin{cases}0,&k=j,\\
--   \det\bigl(\operatorname{updateRow}(\operatorname{updateRow}(A(x),j,c),k,D(A_{k\bullet})_x(v))\bigr),&k\ne j.
--   \end{cases}$$
--
--   The declaration `fderiv_det_updateRow_readable` is used as a local algebraic rule and makes no symmetry, positivity, or invertibility assumption on the matrices.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   private lemma fderiv_det_updateRow
--       {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
--       (A : E → Fin n → Fin n → ℝ) (x : E)
--       (hA : ∀ k l, DifferentiableAt ℝ (fun y => A y k l) x)
--       (j : Fin n) (c : Fin n → ℝ) (v : E) :
--       fderiv ℝ (fun y => (Matrix.updateRow (A y) j c).det) x v =
--         ∑ k, if k = j then 0
--           else ((Matrix.updateRow (A x) j c).updateRow k
--             (fun l => fderiv ℝ (fun y => A y k l) x v)).det
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/Matrix/Piola`](https://prove2.me/theorems/bafaf8f6-610f-44ba-81ae-c118558a1200).
--
--   Next: [`sum_fderiv_adjugate_hessianMatrix_eq_zero`](https://prove2.me/theorems/d9abe498-7a4a-408f-882a-341a822f2253).
--
--   [Source excerpt, lines 57–65](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Matrix/Piola.lean#L57-L65) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Matrix/Piola.lean#L57-L129 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Matrix.Piola`, declaration `_private.FunctionalInequalities.Analysis.Matrix.Piola.0.FunctionalInequalities.Analysis.fderiv_det_updateRow`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Matrix_Piola

lemma FunctionalInequalities.Analysis.fderiv_det_updateRow_readable
    {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A : E → Fin n → Fin n → ℝ) (x : E)
    (hA : ∀ k l, DifferentiableAt ℝ (fun y => A y k l) x)
    (j : Fin n) (c : Fin n → ℝ) (v : E) :
    fderiv ℝ (fun y => (Matrix.updateRow (A y) j c).det) x v =
      ∑ k, if k = j then 0
        else ((Matrix.updateRow (A x) j c).updateRow k
          (fun l => fderiv ℝ (fun y => A y k l) x v)).det := by sorry
