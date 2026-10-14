-- Prove2me | Theorems.Thm_GarrettFA_not_isNetComplete_weakDual_of_isStrictColimit
-- name    : GarrettFA.not_isNetComplete_weakDual_of_isStrictColimit
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-12T19:36:21.365547+00:00
-- url     : https://prove2.me/theorems/8c06a97a-1223-4a4f-9947-ade2841df188
-- title:
--   Cor. 5.0.2 (LF case, corrected) — weak duals of LF-spaces with an infinite-dimensional step are not complete
-- statement:
--   Let $X$ be an LF-space over $\mathbb K=\mathbb R$ or $\mathbb C$: the strict colimit of a chain $X_0\subsetneq X_1\subsetneq\cdots$ of closed subspaces, each metrizable and complete. If some step $X_n$ is infinite-dimensional, then the weak dual of $X$ is not complete.
--
--   This covers the spaces of test functions $C_c^\infty(\mathbb R^n)$, $n\ge1$.
--
--   **Formalization Note** The notes state the corollary for all infinite-dimensional LF-spaces. That is false for the LF-space $\mathbb C^\infty$ of Example 1.3.1, the strict colimit of the finite-dimensional spaces $\mathbb C^n$. Its topology is the finest locally convex topology, so every linear functional is continuous and its weak dual $\mathbb C^{\mathbb N}$ is complete by Theorem 5.0.1. The hypothesis "some step is infinite-dimensional" excludes exactly the LF-spaces of countable dimension.
-- source:
--   Paul Garrett, *Completeness and quasi-completeness* (lecture notes, April 24, 2014), http://www.math.umn.edu/~garrett/m/fun/notes_2012-13/07d_quasi-completeness.pdf, p. 8, Corollary 5.0.2 (LF case; restricted to LF-spaces having an infinite-dimensional step, see the note)

import Definitions.Def_GarrettFA_IsNetComplete
import Definitions.Def_GarrettFA_IsStrictColimit

namespace GarrettFA
theorem not_isNetComplete_weakDual_of_isStrictColimit {𝕜 : Type*} [RCLike 𝕜] {X : Type*} [AddCommGroup X] [Module 𝕜 X] [Module ℝ X]
    [IsScalarTower ℝ 𝕜 X] [UniformSpace X] [IsUniformAddGroup X] [ContinuousSMul 𝕜 X] [T2Space X]
    {F : ℕ → Submodule 𝕜 X} (hF : IsStrictColimit 𝕜 F)
    (hFr : ∀ n, TopologicalSpace.MetrizableSpace (F n) ∧ IsComplete (F n : Set X))
    (hinf : ∃ n, ¬ FiniteDimensional 𝕜 (F n)) :
    ¬ IsNetComplete (WeakDual 𝕜 X) := by sorry
end GarrettFA
