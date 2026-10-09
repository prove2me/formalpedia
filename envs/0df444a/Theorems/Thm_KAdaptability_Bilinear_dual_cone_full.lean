-- Prove2me | Theorems.Thm_KAdaptability_Bilinear_dual_cone_full
-- name    : KAdaptability.Bilinear.dual_cone_full
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T08:05:49.15098+00:00
-- url     : https://prove2.me/theorems/df437cf1-747c-424a-bee6-1cfbc16159f1
-- title:
--   Proof of Theorem 5 — a nonempty bounded Ξ = {ξ : Aξ ≤ b} gives {A⊤α : α ≥ 0} = ℝ^Q
-- statement:
--   Let $A\in\mathbb R^{R\times Q}$ and $b\in\mathbb R^R$ be such that the polyhedron $\Xi=\{\xi\in\mathbb R^Q:A\xi\le b\}$ is nonempty and bounded. Then
--   $$\{A^\top\alpha:\ \alpha\in\mathbb R^R,\ \alpha\ge 0\}=\mathbb R^Q,$$
--   that is, every vector $v\in\mathbb R^Q$ can be written as $v=A^\top\alpha$ with $\alpha\ge0$.
--
--   In the proof of Theorem 5 this is why the dual linear programs of the inner maximizations are always feasible, so that strong duality holds.
--
--   **Formalization Note** The polyhedron is the uncertainty set of the problem data, whose nonemptiness and boundedness are fields of the data structure.
-- source:
--   Hanasusanto, Kuhn, Wiesemann, K-Adaptability in Two-Stage Robust Binary Programming, preprint, Optimization Online 2014/03/4294 (revision of 2015-03-30), p. ec9 (PDF p. 43), Proof of Theorem 5

import Definitions.Def_KAdaptability_Bilinear_Program7

open Matrix

namespace KAdaptability.Bilinear

open Problem

/-- **Proof of Theorem 5, `{A⊤α : α ≥ 0} = ℝ^Q`** (p. ec9). Since `Ξ = {ξ : Aξ ≤ b}` is
nonempty and bounded (fields of `Problem`), every vector of `ℝ^Q` is `A⊤α` for some `α ≥ 0`. -/
theorem dual_cone_full {N M L nQ R : ℕ} (P : Problem N M L nQ R) :
    ∀ v : Fin nQ → ℝ, ∃ α : Fin R → ℝ, 0 ≤ α ∧ P.Aᵀ *ᵥ α = v := by sorry

end KAdaptability.Bilinear
