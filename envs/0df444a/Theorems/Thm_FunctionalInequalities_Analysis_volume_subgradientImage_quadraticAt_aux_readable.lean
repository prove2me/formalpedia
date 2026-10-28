-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_volume_subgradientImage_quadraticAt_aux_readable
-- name    : FunctionalInequalities.Analysis.volume_subgradientImage_quadraticAt_aux_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:04:19.857995+00:00
-- url     : https://prove2.me/theorems/af304715-487f-4a7a-bf76-4a29343dc231
-- title:
--   Volume Formula for Quadratic Subgradient Images
-- statement:
--   This is an auxiliary volume identity for quadratic subgradient images.
--
--   Let $A$ be a positive-definite real $n\times n$ matrix, let $x_0,b\in\operatorname{EuclideanSpace}\,\mathbb R\,(\operatorname{Fin}(n))$, let $c\in\mathbb R$, and let $G$ be any subset of that Euclidean space. Then the Lebesgue volume of the subgradient image of $G$ under `quadraticAt` is
--   $$\operatorname{vol}\bigl(\operatorname{subgradientImage}(\operatorname{quadraticAt}(A,x_0,b,c),G)\bigr)
--   =\operatorname{ofReal}(\det A)\,\operatorname{vol}(G).$$
--
--   The determinant factor is represented as an `ENNReal` value through `ENNReal.ofReal`. This identity is a reusable change-of-variables formula for the affine gradient map of a positive-definite quadratic.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   private lemma volume_subgradientImage_quadraticAt_aux
--       {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef)
--       (x₀ b : EuclideanSpace ℝ (Fin n)) (c : ℝ)
--       {G : Set (EuclideanSpace ℝ (Fin n))} :
--       (volume : Measure (EuclideanSpace ℝ (Fin n)))
--           (subgradientImage (quadraticAt A x₀ b c) G) =
--         ENNReal.ofReal A.det *
--           (volume : Measure (EuclideanSpace ℝ (Fin n))) G
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/Convex/Alexandrov`](https://prove2.me/theorems/3d12d62d-28ee-413a-8964-1771fdfa5905).
--
--   Definition modules: [`Analysis/Convex/Subgradient`](https://prove2.me/theorems/67a77afb-a546-4173-875a-237133f9cad7).
--
--   Supporting theorems: [`quadraticAt_subgradient_iff`](https://prove2.me/theorems/30c05a45-559f-4ce4-9d75-9148915945b6).
--
--   Previous: [`convexOn_quadraticAt`](https://prove2.me/theorems/cc6c84fa-e5eb-4068-927b-9d626453be97) · Next: [`infDist_frontier_le_of_forall_inner_le`](https://prove2.me/theorems/bd9c0578-bb14-4e91-95ff-70001c4a6fce).
--
--   [Source excerpt, lines 1603–1610](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Convex/Alexandrov.lean#L1603-L1610) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Convex/Alexandrov.lean#L1603-L1660 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Convex.Alexandrov`, declaration `_private.FunctionalInequalities.Analysis.Convex.Alexandrov.0.FunctionalInequalities.Analysis.volume_subgradientImage_quadraticAt_aux`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Convex_Alexandrov

open MeasureTheory Set Matrix

lemma FunctionalInequalities.Analysis.volume_subgradientImage_quadraticAt_aux_readable
    {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosDef)
    (x₀ b : EuclideanSpace ℝ (Fin n)) (c : ℝ)
    {G : Set (EuclideanSpace ℝ (Fin n))} :
    (volume : Measure (EuclideanSpace ℝ (Fin n)))
        (subgradientImage (quadraticAt A x₀ b c) G) =
      ENNReal.ofReal A.det *
        (volume : Measure (EuclideanSpace ℝ (Fin n))) G := by sorry
