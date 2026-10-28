-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_hessianMatrix_quadratic_readable
-- name    : FunctionalInequalities.Analysis.hessianMatrix_quadratic_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:04:24.710994+00:00
-- url     : https://prove2.me/theorems/c1a646b2-00af-48f5-80d5-4c01f3dab8bd
-- title:
--   Quadratic Form of the Coordinate Hessian
-- statement:
--   This is a coordinate-identification lemma for the Hessian matrix.
--
--   Let $n\in\mathbb N$, let $\psi:\operatorname{EuclideanSpace}\,\mathbb R\,(\operatorname{Fin}(n))\to\mathbb R$, let $x$ be a point in that space, and let $v$ be a vector. The quadratic form associated with `hessianMatrix ψ x` satisfies
--   $$\left\langle v,\operatorname{toEuclideanLin}(\operatorname{hessianMatrix}(\psi,x))v\right\rangle
--   = D^2\psi(x)[v,v],$$
--   where the right-hand side is expressed in Lean as the iterated Fréchet derivative `(fderiv ℝ (fderiv ℝ ψ) x) v v`.
--
--   The lemma connects the coordinate Hessian representation used by the formalization with the second Fréchet derivative and is intended for later viscosity calculations.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   private lemma hessianMatrix_quadratic
--       {n : ℕ} {ψ : EuclideanSpace ℝ (Fin n) → ℝ}
--       {x : EuclideanSpace ℝ (Fin n)}
--       (v : EuclideanSpace ℝ (Fin n)) :
--       ⟪v, Matrix.toEuclideanLin (hessianMatrix ψ x) v⟫ =
--         (fderiv ℝ (fderiv ℝ ψ) x) v v
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/Convex/Viscosity`](https://prove2.me/theorems/a4ce95cb-0230-40ed-bbee-de7462504a4b).
--
--   Definition modules: [`Analysis/BakryEmery/HessianOperator`](https://prove2.me/theorems/0a60d77a-9d99-47ed-a649-6e1a28e13392).
--
--   Previous: [`posSemidef_hessianMatrix_of_upper_touch`](https://prove2.me/theorems/c0934c18-f16d-42fc-a97b-28fa4ccb6c6d) · Next: [`local_taylor_two`](https://prove2.me/theorems/4b2efc81-f85a-4a3c-aec5-38e536f55203).
--
--   [Source excerpt, lines 209–214](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Convex/Viscosity.lean#L209-L214) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Convex/Viscosity.lean#L209-L259 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Convex.Viscosity`, declaration `_private.FunctionalInequalities.Analysis.Convex.Viscosity.0.FunctionalInequalities.Analysis.hessianMatrix_quadratic`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Convex_Viscosity

open scoped RealInnerProductSpace Topology
open FunctionalInequalities.Probability.Stein

lemma FunctionalInequalities.Analysis.hessianMatrix_quadratic_readable
    {n : ℕ} {ψ : EuclideanSpace ℝ (Fin n) → ℝ}
    {x : EuclideanSpace ℝ (Fin n)}
    (v : EuclideanSpace ℝ (Fin n)) :
    ⟪v, Matrix.toEuclideanLin (hessianMatrix ψ x) v⟫ =
      (fderiv ℝ (fderiv ℝ ψ) x) v v := by sorry
