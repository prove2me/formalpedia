-- Prove2me | Theorems.Thm_HoffmanBound_ErrorBound_lemma2
-- name    : HoffmanBound.ErrorBound.lemma2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T09:36:23.458983+00:00
-- url     : https://prove2.me/theorems/a6c3f9d4-27fb-4c39-9693-62c5d9257775
-- title:
--   Lemma 2 — the nearest solution is also the nearest point of the intersection of the active half spaces
-- statement:
--   Let $\Omega=\{x\in\mathbb R^n : Ax\le b\}$ be the solution set of the system (1), let $x\notin\Omega$, and let $y$ be a point of $\Omega$ nearest to $x$ in the Euclidean distance. Let
--   $$
--   S=\{i : A_i\cdot y=b_i\},\qquad \Omega_S=\{z\in\mathbb R^n : A_i\cdot z\le b_i\ \text{for all } i\in S\}
--   $$
--   be the half spaces of (1) whose bounding hyperplanes contain $y$ and their intersection. Then $x\notin\Omega_S$, and $y$ is a point of $\Omega_S$ nearest to $x$.
--
--   This lemma reduces the error bound to the finitely many sets of active constraints, which is where the uniform constant of the main theorem comes from.
--
--   **Formalization Note** The paper says "the point nearest"; the Euclidean nearest point of a nonempty closed convex set is unique, so the hypothesis is stated as "$y$ is a nearest point" and the conclusion as "$y$ is a nearest point of $\Omega_S$". If $S=\emptyset$, then $\Omega_S=\mathbb R^n$.
-- source:
--   Hoffman, On Approximate Solutions of Systems of Linear Inequalities, J. Res. Nat. Bur. Standards 49 (1952), p. 263 (PDF p. 1), Lemma 2

import Mathlib
import Definitions.Def_HoffmanBound_ErrorBound_Model

namespace HoffmanBound.ErrorBound

open Matrix

/-- Hoffman 1952, p. 263, Lemma 2. Let `Ω` be the solution set of `Ax ≤ b`, `x ∉ Ω`, and `y` a
point of `Ω` nearest to `x` (Euclidean). Let `S` be the set of half spaces whose bounding
hyperplane contains `y` and `Ω_S` their intersection. Then `x ∉ Ω_S` and `y` is a nearest point
of `Ω_S` to `x`. -/
theorem lemma2 {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (x y : Fin n → ℝ)
    (hx : x ∉ solutionSet A b) (hy : IsNearest (solutionSet A b) x y) :
    x ∉ {z : Fin n → ℝ | ∀ i ∈ activeSet A b y, (A *ᵥ z) i ≤ b i} ∧
      IsNearest {z : Fin n → ℝ | ∀ i ∈ activeSet A b y, (A *ᵥ z) i ≤ b i} x y := by sorry

end HoffmanBound.ErrorBound
