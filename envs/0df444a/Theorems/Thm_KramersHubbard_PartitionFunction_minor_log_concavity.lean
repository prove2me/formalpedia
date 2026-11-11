-- Prove2me | Theorems.Thm_KramersHubbard_PartitionFunction_minor_log_concavity
-- name    : KramersHubbard.PartitionFunction.minor_log_concavity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:04:02.903313+00:00
-- url     : https://prove2.me/theorems/c1b47308-788b-4601-9835-d36c0b17acfa
-- title:
--   Lemma 7 — Square-root determinant and joint log-concavity
-- statement:
--   For any quaternionic $G\in\mathbb C^{2p\times2p}$, define $g_G(y,z)=\sum_{|A|=|B|}\det G[A,B]z^Ay^{[p]\setminus B}$. For every strictly positive $y,z\in\mathbb R^p$,
--
--   $$g_G(y,z)=\sqrt{\det(D_y+G^\dagger D_zG)},\qquad\log g_G\text{ is concave on }\mathbb R_{>0}^p\times\mathbb R_{>0}^p.$$
--
--   The determinant under the square root is positive real; the root is its nonnegative real root. Both conclusions apply on the entire product orthant, without a Hermiticity or positive-semidefiniteness assumption on $G$. This is the analytic property needed for the chain's gap bound.
--
--   Differences from the source:
--   - encoding: consecutive scalar rows of square quaternionic matrices → Fin p times Fin 2 whole-block indices, complex determinants and explicit nonnegative real witnesses; reason: both scalar rows and columns of every block are kept; the empty determinant is one
--   - generalization: Section 3 defines J_p for positive integer p → the determinant and polynomial statements also allow p=0; reason: the additional empty-matrix case has determinant one and polynomial one; every positive-dimensional source instance is retained
--   - encoding: joint concavity of the logarithm on the two positive orthants → ConcaveOn on the Cartesian product and an explicit positive real determinant witness; reason: the determinant identity first establishes the real positive value, so Real.log is applied to that value without discarding a complex component
-- source:
--   Chaithanya Rayudu, Jun Takahashi, Ojas Parekh, Andrew Zhao, STOC 2027 submission #1325 (October 2026), Efficient classical simulation of Fermi-Hubbard models with Kramers symmetry, Lemma 7 and Eqs.(43)-(44), p.18; proof p.19; printed page = 1-based PDF page. https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1325.pdf; PDF SHA-256 e3fd3fa7390d8ff9f0f1e2ee07e6ebc5b8d7304e26be9e76959d9587f4564eae. Canonical submitted artifact, citation_basis: published; title-page date November 3, 2026; no assertion of conference acceptance.

import Definitions.Def_KramersHubbard_PartitionFunction_Quaternion

noncomputable section
open scoped BigOperators
open Matrix MeasureTheory

namespace KramersHubbard.PartitionFunction

/-- Lemma 7, p.18: full square-root identity and concavity on BOTH orthants. -/
theorem minor_log_concavity {p : ℕ}
    (G : Matrix (Fin p × Fin 2) (Fin p × Fin 2) ℂ) (hG : Quaternionic G) :
    (∀ y z : Fin p → ℝ, (∀ i, 0 < y i) → (∀ i, 0 < z i) →
      ∃ d : ℝ, 0 < d ∧
        (blockDiagonal y + G.conjTranspose * blockDiagonal z * G).det = (d : ℂ) ∧
        minorPolynomial G y z = (Real.sqrt d : ℂ)) ∧
    ConcaveOn ℝ (positiveOrthant p)
      (fun u => Real.log (minorPolynomial G u.1 u.2).re) := by sorry

end KramersHubbard.PartitionFunction
