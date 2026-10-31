-- Prove2me | Theorems.Thm_KallMayerSLP_ProbConstr_realizationSet_convex_polyhedral
-- name    : KallMayerSLP.ProbConstr.realizationSet_convex_polyhedral
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:10:22.316799+00:00
-- url     : https://prove2.me/theorems/3f54a1a8-7fb5-4882-9a58-32fe0b98c2eb
-- title:
--   p.98 — the sets $K_j$ are convex polyhedral
-- statement:
--   For every realization $\hat\xi\in\mathbb R^r$ the set
--   $$
--   K=\{x\in\mathbb R^n\mid T(\hat\xi)x\ge h(\hat\xi)\}
--   $$
--   is convex, and it is polyhedral: there are vectors $a_1,\dots,a_m\in\mathbb R^n$ and numbers $b_1,\dots,b_m$ with $K=\{x\mid a_k^{\mathsf T}x\ge b_k,\ k=1,\dots,m\}$. In particular the sets $K_j=\{x\mid T(\hat\xi^j)x\ge h(\hat\xi^j)\}$ of a finite discrete distribution are convex polyhedral sets.
--
--   By (2.18), $\mathcal B(\alpha)$ is a finite union of intersections of these sets.
--
--   Differences from the source:
--   - generalization: the sets K_j for the atoms ξ̂^j, with affine data → the set for every realization ξ and arbitrary data T, h; reason: K_j is the case ξ = ξ̂^j, and affine data are a special case
--   - reading: "convex polyhedral sets" → convex, and equal to {x | ∀ k, b_k ≤ a_k ⬝ x} for some a : Fin m → ℝ^n, b : Fin m → ℝ; reason: a polyhedral set is the solution set of finitely many linear inequalities
-- source:
--   Kall & Mayer, Stochastic Linear Programming: Models, Theory, and Computation (Kluwer/Springer 2005), Chapter 2, Chapter 2, §2.2, p.98 (PDF 108), definition of K_j and the sentence following it

import Mathlib
import Definitions.Def_KallMayerSLP_ProbConstr_realizationSet

open Matrix

namespace KallMayerSLP.ProbConstr

/-- The sets `K_j = {x | T(ξ̂^j)x ≥ h(ξ̂^j)}` "are clearly convex polyhedral sets": each is convex
and is the solution set of finitely many linear inequalities `a_k ⬝ x ≥ b_k`.

Kall & Mayer 2005, Chapter 2, §2.2, p.98 (PDF 108), the sentence after the definition of `K_j`.

**Formalization Note.** Stated for every realization `ξ` and arbitrary data `T`, `h`; "polyhedral"
is read as "the intersection of finitely many closed half-spaces `{x | b_k ≤ a_k ⬝ᵥ x}`" (`m`
inequalities, allowing `a_k = 0`). -/
theorem realizationSet_convex_polyhedral {r m n : ℕ} (T : (Fin r → ℝ) → Matrix (Fin m) (Fin n) ℝ)
    (h : (Fin r → ℝ) → Fin m → ℝ) (ξ : Fin r → ℝ) :
    Convex ℝ (realizationSet T h ξ) ∧
      ∃ (a : Fin m → Fin n → ℝ) (b : Fin m → ℝ),
        realizationSet T h ξ = {x | ∀ k, b k ≤ a k ⬝ᵥ x} := by sorry

end KallMayerSLP.ProbConstr
