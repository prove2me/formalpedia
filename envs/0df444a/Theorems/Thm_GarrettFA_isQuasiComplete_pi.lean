-- Prove2me | Theorems.Thm_GarrettFA_isQuasiComplete_pi
-- name    : GarrettFA.isQuasiComplete_pi
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-12T19:33:36.917987+00:00
-- url     : https://prove2.me/theorems/9c96b759-db91-4959-b2f5-07b0073d7a68
-- title:
--   §4 — products of quasi-complete spaces are quasi-complete
-- statement:
--   Let $(E_i)_{i\in\iota}$ be a family of quasi-complete topological vector spaces over $\mathbb K=\mathbb R$ or $\mathbb C$. Then the product
--
--   $$\prod_{i\in\iota} E_i$$
--
--   with the product topology is quasi-complete. Finite sums are the special case of a finite index set.
--
--   **Formalization Note** The index type and the factors live in one common universe.
-- source:
--   Paul Garrett, *Completeness and quasi-completeness* (lecture notes, April 24, 2014), http://www.math.umn.edu/~garrett/m/fun/notes_2012-13/07d_quasi-completeness.pdf, p. 6, remark after Definition 4.0.2 ("Products and finite sums of quasi-complete spaces are quasi-complete")

import Definitions.Def_GarrettFA_IsQuasiComplete

universe u

namespace GarrettFA
theorem isQuasiComplete_pi {𝕜 : Type*} [RCLike 𝕜] {ι : Type u}
    {E : ι → Type u} [∀ i, AddCommGroup (E i)] [∀ i, Module 𝕜 (E i)] [∀ i, Module ℝ (E i)]
    [∀ i, IsScalarTower ℝ 𝕜 (E i)] [∀ i, TopologicalSpace (E i)]
    [∀ i, IsTopologicalAddGroup (E i)] [∀ i, ContinuousSMul 𝕜 (E i)] [∀ i, T2Space (E i)]
    (hE : ∀ i, IsQuasiComplete 𝕜 (E i)) :
    IsQuasiComplete 𝕜 (∀ i, E i) := by sorry
end GarrettFA
