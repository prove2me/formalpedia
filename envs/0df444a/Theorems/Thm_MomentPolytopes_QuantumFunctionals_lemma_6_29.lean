-- Prove2me | Theorems.Thm_MomentPolytopes_QuantumFunctionals_lemma_6_29
-- name    : MomentPolytopes.QuantumFunctionals.lemma_6_29
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T01:02:30.04098+00:00
-- url     : https://prove2.me/theorems/42f5ec83-38e3-4358-a942-3f8e920de651
-- title:
--   Lemma 6.29 — d(I, g†g) ≤ 2n^{3/2} log(nS) for an invertible integer matrix with entries bounded by S
-- statement:
--   Let $g\in\mathrm{GL}(n)$ have integer entries with $|g_{ij}|\le S$ for some real $S\ge1$. Then the affine-invariant distance satisfies
--   $$d(I,g^\dagger g)=\|\log(g^\dagger g)\|_F\ \le\ 2n^{3/2}\log(nS),$$
--   with the natural logarithm.
--
--   This bounds how far an integer group element moves the base point of $\mathrm{PD}(n)$; it controls the constant in the proof of Theorem 6.28.
--
--   Differences from the source:
--   - encoding: g ∈ GL(n) with integer entries → g : Matrix (Fin n) (Fin n) ℤ with det g ≠ 0, cast to ℂ; reason: an integer matrix is invertible over ℂ iff its integer determinant is nonzero
--   - encoding: d(I, g†g) → pdDist 1 (g†g) = ‖log(I^{-1/2} g†g I^{-1/2})‖_F; reason: I^{-1/2} = I; the paper's d(x, y) of §2.2
--   - generalization: GL(n) with n ≥ 1 (the proof treats n ≥ 2 and n = 1) → any n : ℕ, including n = 0; reason: at n = 0 both sides are 0; at n ≥ 1 the statement is the source's
-- source:
--   Doğan, Sakabe, Walter, Convex optimization on moment polytopes, arXiv:2609.06633 (PDF sha256 fcf40771…), p. 45, Lemma 6.29

import Mathlib
import Definitions.Def_MomentPolytopes_QuantumFunctionals_Spectra

set_option autoImplicit false

open scoped ComplexOrder Matrix

namespace MomentPolytopes.QuantumFunctionals

/-- Lemma 6.29 (p. 45). Let `g ∈ GL(n)` have integer entries with `|g_{ij}| ≤ S`, `S ≥ 1`.
Then `d(I, g†g) ≤ 2 n^{3/2} log(nS)` (natural logarithm, affine-invariant distance). -/
theorem lemma_6_29 (n : ℕ) (g : Matrix (Fin n) (Fin n) ℤ) (hg : g.det ≠ 0) (S : ℝ) (hS : 1 ≤ S)
    (hbound : ∀ i j, |((g i j : ℤ) : ℝ)| ≤ S) :
    pdDist 1 ((g.map (Int.cast : ℤ → ℂ))ᴴ * g.map (Int.cast : ℤ → ℂ)) ≤
      2 * (n : ℝ) ^ ((3 : ℝ) / 2) * Real.log (n * S) := by sorry

end MomentPolytopes.QuantumFunctionals
