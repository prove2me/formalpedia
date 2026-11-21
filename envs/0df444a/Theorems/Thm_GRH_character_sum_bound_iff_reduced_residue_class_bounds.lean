-- Prove2me | Theorems.Thm_GRH_character_sum_bound_iff_reduced_residue_class_bounds
-- name    : GRH.character_sum_bound_iff_reduced_residue_class_bounds
-- status  : Proved
-- author  : @Yi
-- created : 2026-11-21T00:18:37.555174+00:00
-- url     : https://prove2.me/theorems/e378c149-1bfc-4b20-83ff-bec66551df5f
-- title:
--   Character sum bounds are equivalent to bounds in every reduced residue class
-- statement:
--   Fix a positive modulus $q$, a complex sequence $w(k)$, and a real comparison function $g(N)$. The partial sums of $w(k)\chi(k)$ are $O(g(N))$ for every Dirichlet character modulo $q$ if and only if the partial sums of $w$ in each reduced residue class modulo $q$ are $O(g(N))$. Each bound is for fixed modulus and may have a class- or character-dependent constant. Taking $w=\mu$ gives a residue-class formulation of the finite twisted Möbius frontier.
-- source:
--   Finite character orthogonality and Fourier inversion using Mathlib.NumberTheory.DirichletCharacter.Orthogonality.

import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic

open Filter Asymptotics

theorem GRH.character_sum_bound_iff_reduced_residue_class_bounds (q : ℕ) [NeZero q] (w : ℕ → ℂ) (g : ℕ → ℝ) :
    (∀ χ : DirichletCharacter ℂ q,
      (fun N : ℕ ↦ ∑ k ∈ Finset.range (N + 1), χ k * w k) =O[atTop] g) ↔
    (∀ a : ZMod q, IsUnit a →
      (fun N : ℕ ↦ ∑ k ∈ Finset.range (N + 1), if a = (k : ZMod q) then w k else 0) =O[atTop] g) := by sorry
