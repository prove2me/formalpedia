-- Prove2me | Theorems.Thm_HiddenConvexSO_lemma_3
-- name    : HiddenConvexSO.lemma_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T21:30:15.133125+00:00
-- url     : https://prove2.me/theorems/0c873d28-7a96-465a-910e-2ee3eaab4d8b
-- title:
--   Lemma 3 — a loop whose image winds nontrivially forces $(0,0)\in f(\mathrm{SO}(n))$
-- statement:
--   Let $n\ge 3$, let $f:\mathrm{SO}(n)\to\mathbb R^2$ be continuous, and let $\gamma:[0,1]\to\mathrm{SO}(n)$ be a loop based at some $U\in\mathrm{SO}(n)$ such that $f(\gamma(t))\neq(0,0)$ for all $t\in[0,1]$. Then $f_*(\gamma)=f\circ\gamma$ is a loop in the punctured plane $\mathbb R^2\setminus(0,0)$, and
--
--   $$
--   [f_*(\gamma)]\neq 1\ \text{ in } \pi_1\bigl(\mathbb R^2\setminus(0,0),\,f(U)\bigr)\quad\Longrightarrow\quad (0,0)\in f(\mathrm{SO}(n)).
--   $$
--
--   Since $\pi_1(\mathrm{SO}(n))=\mathbb Z/2\mathbb Z$ for $n\ge 3$, the doubled loop $\gamma\cdot\gamma$ contracts in $\mathrm{SO}(n)$; a contraction that missed the origin under $f$ would contract the nontrivial loop $f_*(\gamma\cdot\gamma)$ in the punctured plane. Adding a translation to $f$, the same holds with any point $\beta\in\mathbb R^2$ in place of the origin. Lemma 3 is the topological step of the proof of Theorem 3.
--
--   **Formalization Note** $\mathrm{SO}(n)$ is the subtype `Matrix.specialOrthogonalGroup (Fin n) ℝ`; $\gamma$ is a Mathlib `Path U U`; $f_*(\gamma)$ is `imageLoop f hf γ hγ`; "not equivalent to the identity element" is `¬ (imageLoop …).Homotopic (Path.refl _)` (homotopy rel endpoints).
--
--   Differences from the source:
--   - reading: two loops are equivalent if there is a continuous T : [0,1]² → X with T(0,·) = γ₁, T(1,·) = γ₂ (p.13, no endpoint condition) → Path.Homotopic: homotopy rel endpoints (fixed base point at every stage); reason: read literally, any two loops in a path-connected space are equivalent (T(s,t) = γ₁((1−s)t) contracts γ₁ to a point, then reverse for γ₂), which would make π₁(ℝ² ∖ 0) trivial against the paper's own claim that it is ℤ (p.13); the based homotopy is the standard definition of π₁ in the cited reference [17] and the one the proofs use
--   - encoding: SO(n) = {X ∈ ℝ^{n×n} : XᵀX = I, det X = 1} with the subspace topology (p.1, p.13) → Matrix.specialOrthogonalGroup (Fin n) ℝ (star A * A = 1 ∧ A * star A = 1 ∧ det A = 1), coerced subtype topology; 0-based indices; reason: Lean convention; for real square matrices AᵀA = I already gives AAᵀ = I, so the same set
--   - encoding: γ a loop at the designated base point of SO(n) → γ : Path U U for an arbitrary U ∈ SO(n); reason: the paper's base point is unspecified; quantifying over every base point covers it
-- source:
--   Ramachandran, Shu & Wang, Hidden convexity, optimization, and algorithms on rotation matrices, arXiv:2304.08596v2, Lemma 3, p.13

import Mathlib
import Definitions.Def_HiddenConvexSO_imageLoop

namespace HiddenConvexSO

/-- **Lemma 3: a loop whose image winds nontrivially around the origin forces the origin into the
image.**
Ramachandran, Shu & Wang, arXiv:2304.08596v2, Lemma 3, p.13 (PDF p.13): "Let n ≥ 3. Suppose
f : SO(n) → R2 is a continuous map and γ : [0, 1] → SO(n) is a loop such that (0, 0) is not in the
image (f∗(γ))([0, 1]). In this case, we may view f∗(γ) as a loop in R2 \ (0, 0). If f∗(γ) is not
equivalent to the identity element in π1(R2 \ (0, 0)), then (0, 0) ∈ f(SO(n))."

**Formalization Note.** SO(n) is the subtype of `Matrix.specialOrthogonalGroup (Fin n) ℝ` with the
subspace topology; `ℝ²` is `ℝ × ℝ`. The loop `γ` is a Mathlib `Path U U` at an arbitrary base point
`U ∈ SO(n)`. `imageLoop f hf γ hγ` is `f∗(γ)` viewed in `{p : ℝ × ℝ // p ≠ 0}`; "not equivalent to
the identity element" is "not homotopic rel endpoints to the constant loop" (`Path.Homotopic`). -/
theorem lemma_3 (n : ℕ) (hn : 3 ≤ n)
    (f : Matrix.specialOrthogonalGroup (Fin n) ℝ → ℝ × ℝ) (hf : Continuous f)
    {U : Matrix.specialOrthogonalGroup (Fin n) ℝ} (γ : Path U U) (hγ : ∀ t, f (γ t) ≠ 0)
    (hnontriv : ¬ (imageLoop f hf γ hγ).Homotopic (Path.refl _)) :
    ∃ X : Matrix.specialOrthogonalGroup (Fin n) ℝ, f X = 0 := by sorry

end HiddenConvexSO
