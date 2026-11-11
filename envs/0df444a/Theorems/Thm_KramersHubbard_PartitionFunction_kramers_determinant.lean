-- Prove2me | Theorems.Thm_KramersHubbard_PartitionFunction_kramers_determinant
-- name    : KramersHubbard.PartitionFunction.kramers_determinant
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:04:01.975553+00:00
-- url     : https://prove2.me/theorems/02180e51-b892-4573-8d9d-dc6422358052
-- title:
--   Lemma 4 — Kramers determinant positivity
-- statement:
--   Let $Q$ be any square quaternionic matrix of complex dimension $2p$, with consecutive $2\times2$ blocks of the form $\left(\begin{smallmatrix}\alpha&-\overline\gamma\\\gamma&\overline\alpha\end{smallmatrix}\right)$. Then
--
--   $$\det Q\in\mathbb R_{\ge0}.$$
--
--   The assertion includes reality of the determinant and requires neither Hermiticity nor positive semidefiniteness. It applies to all square whole-block submatrices, including nonprincipal minors. The empty-matrix extension has determinant one.
--
--   Differences from the source:
--   - encoding: consecutive scalar rows of square quaternionic matrices → Fin p times Fin 2 whole-block indices, complex determinants and explicit nonnegative real witnesses; reason: both scalar rows and columns of every block are kept; the empty determinant is one
--   - generalization: Section 3 defines J_p for positive integer p → the determinant statement also allows p=0; reason: the additional empty-matrix case has determinant one; every positive-dimensional source instance is retained
-- source:
--   Chaithanya Rayudu, Jun Takahashi, Ojas Parekh, Andrew Zhao, STOC 2027 submission #1325 (October 2026), Efficient classical simulation of Fermi-Hubbard models with Kramers symmetry, Lemma 4, p.12; Eqs.(12)-(13), p.11; printed page = 1-based PDF page. https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1325.pdf; PDF SHA-256 e3fd3fa7390d8ff9f0f1e2ee07e6ebc5b8d7304e26be9e76959d9587f4564eae. Canonical submitted artifact, citation_basis: published; title-page date November 3, 2026; no assertion of conference acceptance.

import Definitions.Def_KramersHubbard_PartitionFunction_Quaternion

noncomputable section
open scoped BigOperators
open Matrix MeasureTheory

namespace KramersHubbard.PartitionFunction

/-- Lemma 4, p.12: reality AND nonnegativity, without Hermiticity. -/
theorem kramers_determinant {p : ℕ}
    (Q : Matrix (Fin p × Fin 2) (Fin p × Fin 2) ℂ) (hQ : Quaternionic Q) :
    ∃ d : ℝ, 0 ≤ d ∧ Q.det = (d : ℂ) := by sorry

end KramersHubbard.PartitionFunction
