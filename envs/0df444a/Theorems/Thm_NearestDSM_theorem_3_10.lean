-- Prove2me | Theorems.Thm_NearestDSM_theorem_3_10
-- name    : NearestDSM.theorem_3_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:21:24.576164+00:00
-- url     : https://prove2.me/theorems/83896a70-849c-4a94-a880-6f30ffa902da
-- title:
--   Theorem 3.10 — $y$ is a vertex of $[\tilde y]$ iff its maximal $M$ is connected
-- statement:
--   Let $\tilde y\in\mathbb R^{2n-1}$, let $y\in[\tilde y]$, and let $M$ be maximal for $y$ (that is, $M\in\mathcal M(y)$ and $(\hat x+A^Ty)_{ij}\ge0\Rightarrow M_{ij}=1$). Then
--   $$
--   y\ \text{is a vertex of the polyhedron }[\tilde y]\iff M\ \text{is connected}.
--   $$
--   Combined with Lemma 2.3, at a vertex the maximal element of the generalized Jacobian is nonsingular, which is what makes Algorithm 3.1 well defined.
--
--   **Formalization Note** A vertex is an extreme point.
--
--   Differences from the source:
--   - encoding: size $n\ge1$ → `n + 1`; vertex → extreme point; reason: Lean convention, same instances
-- source:
--   Hu, Im, Li & Wolkowicz, A Semismooth Newton-Type Method for the Nearest Doubly Stochastic Matrix Problem, arXiv:2107.09631v1, Theorem 3.10, p.17 (maximality (3.9), p.17)

import Mathlib
import Definitions.Def_NearestDSM_equivClass
import Definitions.Def_NearestDSM_IsMaximalM
import Definitions.Def_NearestDSM_IsConnectedMat

namespace NearestDSM

/-- Hu, Im, Li & Wolkowicz, arXiv:2107.09631v1, Theorem 3.10, p.17. Let `ỹ ∈ ℝ^{2n−1}` be given, `y ∈ [ỹ]`, and let `M` be
maximal for `y` (3.9). The vector `y` is a vertex of the polyhedron `[ỹ]` if, and only if, `M` is
connected.

**Formalization Note.** A vertex is an extreme point (`Set.extremePoints ℝ`). "Maximal for `y`"
is `M ∈ M(y)` with `(x̂ + Aᵀy)_{ij} ≥ 0 ⟹ M_{ij} = 1` (`IsMaximalM`). The paper's size `n` is
`n + 1`. -/
theorem theorem_3_10 {n : ℕ} (Xh : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (yt y : Dual n) (hy : y ∈ equivClass Xh yt)
    (M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (hM : IsMaximalM Xh y M) :
    y ∈ Set.extremePoints ℝ (equivClass Xh yt) ↔ IsConnectedMat M := by sorry

end NearestDSM
