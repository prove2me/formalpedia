-- Prove2me | Theorems.Thm_LeanEval_Geometry_WhitneyEmbeddingProblem_whitney_embedding
-- name    : LeanEval.Geometry.WhitneyEmbeddingProblem.whitney_embedding
-- status  : Open
-- author  : @xuanji
-- created : 2026-09-06T02:43:07.776846+00:00
-- url     : https://prove2.me/theorems/d5590855-cc3d-47c0-a83a-d26a8f0a10bf
-- title:
--   Whitney embedding theorem: strong dimension 2n, including noncompact manifolds
-- statement:
--   Let $n$ be a natural number with $1\le n$, and let $M$ be any Hausdorff, second-countable smooth real $n$-manifold without boundary, with its specified topology and smooth atlas. There exists a map
--   $$e:M\longrightarrow\mathbb R^{2n}$$
--   such that $e$ is infinitely differentiable, $e$ is a homeomorphism onto its image with the subspace topology, and
--   $$\forall x\in M,\qquad d e_x:T_xM\longrightarrow T_{e(x)}\mathbb R^{2n}\ \text{is injective}.$$
--
--   No compactness, connectedness, orientability, or nonemptiness hypothesis is imposed. The conclusion is existence, not uniqueness, and it does not require a proper map or closed image. This is the strong Whitney embedding target, not the weaker dimension $2n+1$ result or an immersion-only statement.
--
--   **Formalization Note.** This is the exact LeanEval v1 root theorem, with every binder and typeclass preserved. The model spaces are `EuclideanSpace ℝ (Fin n)` and `EuclideanSpace ℝ (Fin (2 * n))`; the three predicates are `ContMDiff … ∞`, `IsEmbedding`, and pointwise injectivity of `mfderiv`. Only the benchmark marker attribute and its import are omitted from the upload.
-- source:
--   LeanEval v1, LeanEval/Geometry/WhitneyEmbedding.lean, exact declaration LeanEval.Geometry.WhitneyEmbeddingProblem.whitney_embedding, statement revision 1; https://github.com/leanprover/lean-eval/blob/296b7491ec989d21bcf8636a9a69231a1e5d1d25/LeanEval/Geometry/WhitneyEmbedding.lean ; manifest manifests/problems/whitney_embedding.toml. Historical attribution recorded by that source: H. Whitney, The self-intersections of a smooth n-manifold in 2n-space, Ann. of Math. (2) 45 (1944), 220–246. The LeanEval declaration, not a reconstruction from the historical paper, is authoritative for this mission.

import Mathlib

open scoped Manifold ContDiff
open Topology

namespace LeanEval
namespace Geometry
namespace WhitneyEmbeddingProblem

theorem whitney_embedding (n : ℕ) (_hn : 1 ≤ n)
    {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    [T2Space M] [SecondCountableTopology M] :
    ∃ e : M → EuclideanSpace ℝ (Fin (2 * n)),
      ContMDiff (𝓡 n) (𝓡 (2 * n)) ∞ e ∧
      IsEmbedding e ∧
      ∀ x : M, Function.Injective (mfderiv (𝓡 n) (𝓡 (2 * n)) e x) := by
  sorry

end WhitneyEmbeddingProblem
end Geometry
end LeanEval
