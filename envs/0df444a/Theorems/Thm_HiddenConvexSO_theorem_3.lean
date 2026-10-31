-- Prove2me | Theorems.Thm_HiddenConvexSO_theorem_3
-- name    : HiddenConvexSO.theorem_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:29:46.02041+00:00
-- url     : https://prove2.me/theorems/09d321a4-b618-4ff5-8b39-64a784498e93
-- title:
--   Theorem 3 — every hyperplane section $\mathrm{SO}(n)\cap\{\langle A,X\rangle=c\}$ is connected, $n\ge3$
-- statement:
--   Let $n\ge 3$, $A\in\mathbb R^{n\times n}$ and $c\in\mathbb R$. Then the hyperplane section
--
--   $$
--   \mathrm{SO}(n)\cap\{X\in\mathbb R^{n\times n}:\ \langle A,X\rangle=c\},\qquad \langle A,X\rangle=\operatorname{tr}(A^\top X),
--   $$
--
--   is connected (in the paper's sense: it cannot be split into two nonempty disjoint relatively closed pieces; the empty set is connected).
--
--   This is the technical core of the paper's first main result: it implies Corollary 1 (every linear image of $\mathrm{SO}(n)$ in $\mathbb R^2$ is convex) and the exactness of the convex relaxation of linear optimization over $\mathrm{SO}(n)$ with one linear constraint. For $n=2$ it fails: $\{X\in\mathrm{SO}(2):X_{11}=0\}$ consists of two points.
--
--   **Formalization Note** The section is a subset of `Matrix (Fin n) (Fin n) ℝ` with its standard topology; $\langle A,X\rangle$ is `traceInner A X`; connectedness is `IsPreconnected`. All $A$ and $c$ are covered, including those with an empty section.
--
--   Differences from the source:
--   - reading: connected → IsPreconnected (the empty set counts as connected); reason: the paper defines connectedness in the proof of Theorem 3 (p.16): not connected means there are nonempty disjoint closed U, V covering the set; under this definition the empty set is connected
--   - encoding: SO(n) = {X ∈ ℝ^{n×n} : XᵀX = I, det X = 1} with the subspace topology (p.1, p.13) → Matrix.specialOrthogonalGroup (Fin n) ℝ (star A * A = 1 ∧ A * star A = 1 ∧ det A = 1), coerced subtype topology; 0-based indices; reason: Lean convention; for real square matrices AᵀA = I already gives AAᵀ = I, so the same set
--   - encoding: ⟨A, X⟩ = tr(AᵀX) (p.2) → traceInner A X = Σᵢ Σⱼ A i j * X i j; reason: tr(AᵀX) = Σᵢⱼ Aᵢⱼ Xᵢⱼ; same value for every A, X
-- source:
--   Ramachandran, Shu & Wang, Hidden convexity, optimization, and algorithms on rotation matrices, arXiv:2304.08596v2, Theorem 3, p.12 (also stated on p.5); connectedness as defined in the proof of Theorem 3, p.16

import Mathlib
import Definitions.Def_WainwrightHDS_NucNorm_traceInner

namespace HiddenConvexSO

open WainwrightHDS.NucNorm

/-- **Theorem 3: every hyperplane section of SO(n) is connected, `n ≥ 3`.**
Ramachandran, Shu & Wang, arXiv:2304.08596v2, Theorem 3, p.12 (PDF p.12; also p.5): "Let n ≥ 3,
A ∈ Rn×n, and c ∈ R. Then, the set SO(n) ∩ {X ∈ Rn×n : ⟨A, X⟩ = c} is connected."

**Formalization Note.** `⟨A, X⟩ = tr(AᵀX)` (p.2) is `traceInner A X`. "Connected" is
`IsPreconnected`, the paper's own definition (proof of Theorem 3, p.16: not connected means there are
nonempty disjoint closed `U, V` covering the set), under which the empty set is connected; this is
needed, since e.g. `A = 0`, `c = 1` gives an empty section. The set lives in `ℝ^{n×n}` with its
standard (product) topology. -/
theorem theorem_3 (n : ℕ) (hn : 3 ≤ n) (A : Matrix (Fin n) (Fin n) ℝ) (c : ℝ) :
    IsPreconnected ((Matrix.specialOrthogonalGroup (Fin n) ℝ : Set (Matrix (Fin n) (Fin n) ℝ)) ∩
      {X | traceInner A X = c}) := by sorry

end HiddenConvexSO
