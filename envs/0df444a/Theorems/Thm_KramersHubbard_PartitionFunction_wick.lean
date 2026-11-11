-- Prove2me | Theorems.Thm_KramersHubbard_PartitionFunction_wick
-- name    : KramersHubbard.PartitionFunction.wick
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T07:04:04.464204+00:00
-- url     : https://prove2.me/theorems/87df08b6-b2f8-4bce-b8fc-19712ac6f54b
-- title:
--   Lemma 5 — Thermal Wick determinant and free partition function
-- statement:
--   Let $H_0=a^\dagger ha$ be the free part of any attractive Kramers input, and let $\beta>0$. Write $Z_0=\operatorname{Tr}e^{-\beta H_0}$, $\rho=(I+e^{\beta h})^{-1}$ and $\langle O\rangle=\operatorname{Tr}(e^{-\beta H_0}O)/Z_0$. For arbitrary vectors $x_1,\ldots,x_n,y_1,\ldots,y_n$, form $G_{ji}=y_j^\dagger\rho x_i$ for $j\ge i$ and $G_{ji}=-y_j^\dagger(I-\rho)x_i$ for $j<i$. Then
--
--   $$\left\langle\prod_{i=1}^n a(x_i)^\dagger a(y_i)\right\rangle=\det G,\qquad Z_0=\det(I+e^{-\beta h}).$$
--
--   The operator product is in increasing index order. The empty product is included. These are the thermal determinant identity and the free normalization needed to connect interaction weights to scalar minors.
--
--   Differences from the source:
--   - encoding: complex Fock operators and one-based mode labels → occupation-basis matrices and zero-based Fin labels, with complex equalities to explicit real witnesses where needed; reason: the occupation basis is the entire Fock space, including the vacuum, and preserves the ordered CAR conventions
--   - encoding: Eq.(21) and Lemma 5 are separate statements → their two equalities are conjoined in one item; reason: both are explicit source claims, with no connecting fact assumed as a hypothesis
-- source:
--   Chaithanya Rayudu, Jun Takahashi, Ojas Parekh, Andrew Zhao, STOC 2027 submission #1325 (October 2026), Efficient classical simulation of Fermi-Hubbard models with Kramers symmetry, Lemma 5, p.14, Eqs.(28)-(29); Eq.(21), p.13; printed page = 1-based PDF page. https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1325.pdf; PDF SHA-256 e3fd3fa7390d8ff9f0f1e2ee07e6ebc5b8d7304e26be9e76959d9587f4564eae. Canonical submitted artifact, citation_basis: published; title-page date November 3, 2026; no assertion of conference acceptance.

import Definitions.Def_KramersHubbard_PartitionFunction_Model

noncomputable section
open scoped BigOperators
open Matrix MeasureTheory

namespace KramersHubbard.PartitionFunction

/-- Lemma 5 and the free partition identity in Eq.(21), pp.13-14. -/
theorem wick {N r n : ℕ} (D : Data N r) (hD : Attractive D)
    (β : ℝ) (hβ : 0 < β) (x y : Fin n → Vec N) :
    thermal D β (((List.finRange n).map fun i =>
      (annihilate (x i)).conjTranspose * annihilate (y i)).prod) = (wickMatrix D β x y).det ∧
    freeZ D β = (1 + NormedSpace.exp ((-β : ℂ) • D.h)).det := by sorry

end KramersHubbard.PartitionFunction
