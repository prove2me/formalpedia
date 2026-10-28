-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_convexOn_quadraticAt_readable
-- name    : FunctionalInequalities.Analysis.convexOn_quadraticAt_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:04:15.569983+00:00
-- url     : https://prove2.me/theorems/cc6c84fa-e5eb-4068-927b-9d626453be97
-- title:
--   Convexity of Positive Semidefinite Quadratics
-- statement:
--   This proves convexity of a quadratic with positive semidefinite matrix.
--
--   Let $n\in\mathbb N$, let $A$ be a real $n\times n$ matrix indexed by `Fin n`, and assume $A$ is positive semidefinite. For any $x_0,b\in\operatorname{EuclideanSpace}(\mathbb R,\operatorname{Fin}n)$ and $c\in\mathbb R$, the function `quadraticAt A x₀ b c` is convex on the whole space:
--   $$\operatorname{ConvexOn}\bigl(\mathbb R,\operatorname{univ},\operatorname{quadraticAt}(A,x_0,b,c)\bigr).$$
--
--   This is a finite-dimensional algebraic lemma for constructing convex quadratic potentials. No positivity or dimension restriction on $n$ is assumed.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem convexOn_quadraticAt {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosSemidef)
--       (x₀ b : EuclideanSpace ℝ (Fin n)) (c : ℝ) : ConvexOn ℝ univ (quadraticAt A x₀ b c)
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/Convex/Alexandrov`](https://prove2.me/theorems/3d12d62d-28ee-413a-8964-1771fdfa5905).
--
--   Previous: [`quadraticAt_subgradient_iff`](https://prove2.me/theorems/30c05a45-559f-4ce4-9d75-9148915945b6) · Next: [`volume_subgradientImage_quadraticAt_aux`](https://prove2.me/theorems/af304715-487f-4a7a-bf76-4a29343dc231).
--
--   [Source excerpt, lines 1585–1586](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Convex/Alexandrov.lean#L1585-L1586) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Convex/Alexandrov.lean#L1584-L1601 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Convex.Alexandrov`, declaration `FunctionalInequalities.Analysis.convexOn_quadraticAt`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Convex_Alexandrov

open MeasureTheory Set Matrix

theorem FunctionalInequalities.Analysis.convexOn_quadraticAt_readable {n : ℕ} {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.PosSemidef)
    (x₀ b : EuclideanSpace ℝ (Fin n)) (c : ℝ) : ConvexOn ℝ univ (quadraticAt A x₀ b c) := by sorry
