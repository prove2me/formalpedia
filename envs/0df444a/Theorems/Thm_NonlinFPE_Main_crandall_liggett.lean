-- Prove2me | Theorems.Thm_NonlinFPE_Main_crandall_liggett
-- name    : NonlinFPE.Main.crandall_liggett
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T02:31:44.841993+00:00
-- url     : https://prove2.me/theorems/c89c782d-ee63-403e-be5c-fa29cd013e17
-- title:
--   Crandall–Liggett theorem (cited, [1] p. 99), §3, p. 8 — an m-accretive A generates a unique mild solution for each u₀ in the closure of D(A); contraction and semigroup
-- statement:
--   Let $\mathcal X$ be a real Banach space and $A$ an m-accretive operator on $\mathcal X$. Then:
--
--   1. for each $u_0 \in \overline{D(A)}$ there is a unique mild solution $u \in C([0,\infty);\mathcal X)$ of (3.2);
--   2. two mild solutions satisfy $\|u(t) - w(t)\|_{\mathcal X} \le \|u(0) - w(0)\|_{\mathcal X}$ for all $t \ge 0$;
--   3. the solution map is a semigroup: if $u$ is the mild solution starting at $u_0$, then $t \mapsto u(t+s)$ is the mild solution starting at $u(s)$.
--
--   So $u_0 \mapsto u(t)$ is a continuous semigroup of contractions on $\overline{D(A)}$. The paper cites this theorem (Barbu, *Nonlinear Differential Equations of Monotone Type in Banach Spaces*, Springer 2010, p. 99) and uses it for Theorems 3.4 and 3.7.
--
--   **Formalization Note** Stated for an operator given by its graph on any real Banach space; mild solutions are those of the mission's `IsMildSolution`.
-- source:
--   Barbu, Röckner, From nonlinear Fokker-Planck equations to solutions of distribution dependent SDE, arXiv:1808.10706v4, §3, p. 8 ("By the Crandall and Liggett theorem (see, e.g., [1], p. 99) …")

import Mathlib
import Definitions.Def_NonlinFPE_Main_Setting
import Definitions.Def_NonlinFPE_Main_MAccretive

open MeasureTheory
open scoped NNReal

namespace NonlinFPE.Main

/-- The Crandall–Liggett theorem as cited on p. 8 ([1], p. 99): if `A` is m-accretive in a real
Banach space `X`, then for each `u₀` in the closure of `D(A)` there is a unique mild solution
`u ∈ C([0, ∞); X)` of (3.2); two mild solutions satisfy `‖u(t) - w(t)‖ ≤ ‖u(0) - w(0)‖`, and
`u₀ ↦ u(t)` is a semigroup: `t ↦ u(t + s)` is the mild solution started at `u(s)`. -/
theorem crandall_liggett {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    (A : X → X → Prop) (hA : IsMAccretive A) :
    (∀ u₀ ∈ closure {u : X | ∃ v, A u v}, ∃! u : ℝ≥0 → X, IsMildSolution A u₀ u) ∧
    (∀ (u₀ w₀ : X) (u w : ℝ≥0 → X), IsMildSolution A u₀ u → IsMildSolution A w₀ w →
      ∀ t, ‖u t - w t‖ ≤ ‖u₀ - w₀‖) ∧
    (∀ (u₀ : X) (u : ℝ≥0 → X), IsMildSolution A u₀ u →
      ∀ s : ℝ≥0, IsMildSolution A (u s) (fun t => u (t + s))) := by sorry

end NonlinFPE.Main
