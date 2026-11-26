-- Prove2me | Theorems.Thm_LefebvreVariations_whitney_closed_embedding_two_n_plus_one
-- name    : LefebvreVariations.whitney_closed_embedding_two_n_plus_one
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-26T21:34:35.585804+00:00
-- url     : https://prove2.me/theorems/45dafaf1-c607-42d7-b5fd-457325d8ec68
-- title:
--   Lefebvre's variations, No. 221 — on a theme by Whitney: every smooth n-manifold has a closed embedding into Euclidean space of dimension 2n+1
-- statement:
--   Let $n\ge 0$ and let $M$ be a smooth, Hausdorff, second-countable $n$-manifold without boundary (compact or not). Then there is a smooth map $e\colon M\to\mathbb{R}^{2n+1}$ which is a closed embedding (a homeomorphism onto a closed subset) and an immersion:
--   $$\exists\, e\in C^\infty(M,\mathbb{R}^{2n+1}):\quad e \text{ is a closed embedding and } de_x \text{ is injective } \forall x\in M .$$
--
--   This is the easy form of Whitney's embedding theorem. The sharp dimension $2n$ is the open platform problem; the dimension $2n+1$ is the stepping stone from which Whitney's trick of removing double points starts.
--
--   **Formalization Note** `M : Type*` with `[TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M] [T2Space M] [SecondCountableTopology M]`; the conclusion gives `e : M → EuclideanSpace ℝ (Fin (2 * n + 1))` with `ContMDiff (𝓡 n) (𝓡 (2 * n + 1)) ∞ e`, `IsClosedEmbedding e` and injective `mfderiv (𝓡 n) (𝓡 (2 * n + 1)) e x` for all `x`. Compactness of `M` is not assumed, and `n = 0` is allowed (a countable discrete space embeds as a closed discrete subset of `ℝ`).
--
--   **Why this is a variation.** Weak form of the open platform problem LeanEval.Geometry.WhitneyEmbeddingProblem.whitney_embedding: embedding in R^(2n+1) instead of R^(2n), with a closed image, for all second-countable Hausdorff smooth manifolds (compact or not). It is the stepping stone before Whitney's double-point removal; not a formal consequence of the parent.
--
--   **Attribution.** This statement belongs to *Lefebvre's variations*, a series proposed by Erwan Lefebvre: each variation plays an open problem of the platform at its first non-trivial size, so that it can be settled and then reused to attack the open problem itself.
-- source:
--   Parent (mathematical): the strong Whitney embedding theorem, LeanEval.Geometry.WhitneyEmbeddingProblem.whitney_embedding (open on the platform, target R^(2n)). This is the classical weak form with target R^(2n+1) and a closed image; it is not a formal consequence of the parent (target dimension 2n+1 instead of 2n, closedness added). The platform has the compact case (WhitneyEmbedding.compact_weak_embedding); this statement drops compactness.
--   Source: H. Whitney, 'Differentiable manifolds', Ann. of Math. 37 (1936), 645-680 (cited from memory); textbook proof of the proper embedding in R^(2n+1): J. M. Lee, 'Introduction to Smooth Manifolds', Whitney embedding theorem (cited from memory).

import Mathlib

set_option autoImplicit false

open scoped Manifold ContDiff
open Topology

namespace LefebvreVariations

/-- Whitney's easy embedding theorem: every second-countable smooth `n`-manifold admits a smooth
immersion which is a closed embedding in `ℝ²ⁿ⁺¹`. This is the weak form of
`LeanEval.Geometry.WhitneyEmbeddingProblem.whitney_embedding` (dimension `2n` replaced by `2n + 1`,
the target being closed). -/
theorem whitney_closed_embedding_two_n_plus_one (n : ℕ)
    {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    [T2Space M] [SecondCountableTopology M] :
    ∃ e : M → EuclideanSpace ℝ (Fin (2 * n + 1)),
      ContMDiff (𝓡 n) (𝓡 (2 * n + 1)) ∞ e ∧ IsClosedEmbedding e ∧
      ∀ x : M, Function.Injective (mfderiv (𝓡 n) (𝓡 (2 * n + 1)) e x) := by
  sorry

end LefebvreVariations
