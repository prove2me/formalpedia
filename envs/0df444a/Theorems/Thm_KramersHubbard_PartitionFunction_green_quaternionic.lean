-- Prove2me | Theorems.Thm_KramersHubbard_PartitionFunction_green_quaternionic
-- name    : KramersHubbard.PartitionFunction.green_quaternionic
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:05:58.15717+00:00
-- url     : https://prove2.me/theorems/b17ff055-75c3-4374-8f4f-771075d6ef38
-- title:
--   Lemma 6 — Quaternionic Green matrix and Eq.(33)
-- statement:
--   For an attractive Kramers input, $\beta>0$ and an integer $M\ge1$, construct the Green matrix $G$ from the time-evolved Kramers-pair columns in Eqs.(30)-(32). Then
--
--   $$G\text{ is quaternionic},\qquad f(X)=Z_0\det G[X]\quad(X\subseteq K),\qquad \operatorname{Tr}L^M=Z_0\sum_{X\subseteq K}\det G[X].$$
--
--   Here $f$ is the direct ordered operator expansion in Eq.(20), not a quantity defined by this identity. No restriction to Hermitian Green matrices or strictly positive couplings is made. This supplies the concrete matrix symmetry and the connection from the physical trace to its minors.
--
--   Differences from the source:
--   - encoding: complex Fock operators and one-based mode labels → occupation-basis matrices and zero-based Fin labels, with complex equalities to explicit real witnesses where needed; reason: the occupation basis is the entire Fock space, including the vacuum, and preserves the ordered CAR conventions
--   - encoding: the source writes scalar products in a chosen Kramers basis → the same scalar products are computed in the input basis; reason: unitary basis changes leave all these scalar products unchanged and no basis computation is supplied for free
--   - encoding: Lemma 6 and Eq.(33) are adjacent claims → quaternionicity and both expansion equalities are conjoined; reason: the source connecting facts remain conclusions rather than input promises
-- source:
--   Chaithanya Rayudu, Jun Takahashi, Ojas Parekh, Andrew Zhao, STOC 2027 submission #1325 (October 2026), Efficient classical simulation of Fermi-Hubbard models with Kramers symmetry, Lemma 6 and Eq.(33), p.15; Eqs.(20), (30)-(32), pp.13-15; printed page = 1-based PDF page. https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1325.pdf; PDF SHA-256 e3fd3fa7390d8ff9f0f1e2ee07e6ebc5b8d7304e26be9e76959d9587f4564eae. Canonical submitted artifact, citation_basis: published; title-page date November 3, 2026; no assertion of conference acceptance.

import Definitions.Def_KramersHubbard_PartitionFunction_Green

noncomputable section
open scoped BigOperators
open Matrix MeasureTheory

namespace KramersHubbard.PartitionFunction

/-- Lemma 6 and Eq.(33), p.15. Scalar products are basis independent, so a
    Kramers-basis computation is not assumed as a free algorithmic operation. -/
theorem green_quaternionic {N r M : ℕ} (D : Data N r) (hD : Attractive D)
    (β : ℝ) (hβ : 0 < β) (hM : 0 < M) :
    Quaternionic (green (M := M) D β) ∧
    (∀ X : Finset (Insertion M r), expansionWeight D β X =
      freeZ D β * blockDet (green D β) X X) ∧
    trotterZ D β M = freeZ D β *
      ∑ X : Finset (Insertion M r), blockDet (green D β) X X := by sorry

end KramersHubbard.PartitionFunction
