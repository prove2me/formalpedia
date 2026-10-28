-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_quadraticAt_subgradient_iff_readable
-- name    : FunctionalInequalities.Analysis.quadraticAt_subgradient_iff_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:04:07.62725+00:00
-- url     : https://prove2.me/theorems/30c05a45-559f-4ce4-9d75-9148915945b6
-- title:
--   Subgradient Characterization of a Positive Semidefinite Quadratic
-- statement:
--   This is a technical characterization of subgradients of the quadratic function `quadraticAt`.
--
--   Let $n\in\mathbb N$, let $A$ be a positive semidefinite real matrix indexed by $\operatorname{Fin}(n)$, and let $x_0,b,x,p\in\operatorname{EuclideanSpace}\,\mathbb R\,(\operatorname{Fin}(n))$. For $c\in\mathbb R$, the following are equivalent:
--
--   1. for every $y$,
--   $$q(x)+\langle p,y-x\rangle\le q(y),$$
--   where $q(z)=\operatorname{quadraticAt}(A,x_0,b,c,z)$;
--   2. $p=b+A(x-x_0)$, with $A$ interpreted through `Matrix.toEuclideanLin`.
--
--   Thus,
--   $$\bigl(\forall y,\ q(x)+\langle p,y-x\rangle\le q(y)\bigr)\iff p=b+A(x-x_0).$$
--
--   The lemma gives the exact affine formula for every subgradient of this positive semidefinite quadratic, including the degenerate case.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   private lemma quadraticAt_subgradient_iff {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
--       (hA : A.PosSemidef) (x₀ b : EuclideanSpace ℝ (Fin n)) (c : ℝ)
--       (x p : EuclideanSpace ℝ (Fin n)) :
--       (∀ y, quadraticAt A x₀ b c x + ⟪p, y - x⟫ ≤ quadraticAt A x₀ b c y) ↔
--         p = b + Matrix.toEuclideanLin A (x - x₀)
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/Convex/Alexandrov`](https://prove2.me/theorems/3d12d62d-28ee-413a-8964-1771fdfa5905).
--
--   Previous: [`exists_pos_alexandrov_maximum_principle`](https://prove2.me/theorems/fb6f8a3c-985d-4638-9d88-5993fe585328) · Next: [`convexOn_quadraticAt`](https://prove2.me/theorems/cc6c84fa-e5eb-4068-927b-9d626453be97).
--
--   [Source excerpt, lines 1470–1474](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Convex/Alexandrov.lean#L1470-L1474) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Convex/Alexandrov.lean#L1470-L1537 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Convex.Alexandrov`, declaration `_private.FunctionalInequalities.Analysis.Convex.Alexandrov.0.FunctionalInequalities.Analysis.quadraticAt_subgradient_iff`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Convex_Alexandrov

open scoped RealInnerProductSpace ENNReal

lemma FunctionalInequalities.Analysis.quadraticAt_subgradient_iff_readable {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : A.PosSemidef) (x₀ b : EuclideanSpace ℝ (Fin n)) (c : ℝ)
    (x p : EuclideanSpace ℝ (Fin n)) :
    (∀ y, quadraticAt A x₀ b c x + ⟪p, y - x⟫ ≤ quadraticAt A x₀ b c y) ↔
      p = b + Matrix.toEuclideanLin A (x - x₀) := by sorry
