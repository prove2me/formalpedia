-- Prove2me | Theorems.Thm_InvariantSDP_BlockDiag_decomp_simple
-- name    : InvariantSDP.BlockDiag.decomp_simple
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T13:39:37.69533+00:00
-- url     : https://prove2.me/theorems/1464327e-d586-4c8b-a81a-17034a7b72c3
-- title:
--   p. 14 — $\mathcal A=\bigoplus_{i=1}^d E_i\mathcal A$ with $E_i$ the minimal idempotents of $\mathcal C_{\mathcal A}$ and each $E_i\mathcal A$ simple
-- statement:
--   Every matrix ∗-algebra $\mathcal A \subseteq \mathbb C^{n\times n}$ is the direct sum of simple matrix ∗-algebras:
--   $$\mathcal A = \bigoplus_{i=1}^d E_i \mathcal A,$$
--   where $E_1, \dots, E_d$ are the minimal idempotents of the center $\mathcal C_{\mathcal A}$. Precisely, there are $d \ge 0$ and matrices $E_1, \dots, E_d$ such that
--
--   1. each $E_i$ lies in the center $\mathcal C_{\mathcal A}$;
--   2. $E_iE_j = \delta_{ij} E_i$ for all $i, j$;
--   3. each $E_i$ is nonzero;
--   4. $E_1, \dots, E_d$ span $\mathcal C_{\mathcal A}$;
--   5. each $E_i\mathcal A = \{E_iX : X \in \mathcal A\}$ is a simple matrix ∗-algebra;
--   6. $X = E_1X + \dots + E_dX$ for every $X \in \mathcal A$.
--
--   Items 1–4 say that $E_1,\dots,E_d$ are exactly the minimal idempotents of $\mathcal C_{\mathcal A}$ (the center is then $\cong \mathbb C^d$ with these as its coordinate idempotents). Item 6, together with 2, is the direct-sum decomposition; the summand $\{0\}$ of the paper's refined form $\mathcal A = \{0\} \oplus E_1\mathcal A \oplus \dots \oplus E_d\mathcal A$ is the zero block on the common kernel and is invisible inside $\mathcal A$. Combined with the fact that every simple matrix ∗-algebra is ∗-isomorphic to a full matrix algebra, this yields Theorem 2.7.
--
--   **Formalization Note** Each $E_i\mathcal A$ is given as a `NonUnitalStarSubalgebra` `C i` whose carrier is required to equal $\{E_iX : X \in \mathcal A\}$; simplicity is the mission's `IsSimple` (non-zero, with a unit $E$ and center $\mathbb C E$). $d = 0$ covers $\mathcal A = \{0\}$.
-- source:
--   Bachoc, Gijswijt, Schrijver & Vallentin, Invariant semidefinite programs, arXiv:1007.2905v2, p. 14, paragraph after the terminology of Theorem 2.7 and the block structure in its proof

import Mathlib
import Definitions.Def_InvariantSDP_BlockDiag_Basic

namespace InvariantSDP.BlockDiag

/-- p. 14: every matrix ∗-algebra is the direct sum `𝒜 = E₁𝒜 ⊕ ⋯ ⊕ E_d𝒜` of simple matrix ∗-algebras,
where `E₁, …, E_d` are the minimal idempotents of the center `𝒞_𝒜`. -/
theorem decomp_simple {n : ℕ} (A : NonUnitalStarSubalgebra ℂ (Matrix (Fin n) (Fin n) ℂ)) :
    ∃ (d : ℕ) (E : Fin d → Matrix (Fin n) (Fin n) ℂ)
      (C : Fin d → NonUnitalStarSubalgebra ℂ (Matrix (Fin n) (Fin n) ℂ)),
      (∀ i, E i ∈ center A) ∧
      (∀ i j, E i * E j = if i = j then E i else 0) ∧
      (∀ i, E i ≠ 0) ∧
      (∀ Z ∈ center A, ∃ c : Fin d → ℂ, Z = ∑ i, c i • E i) ∧
      (∀ i, (C i : Set (Matrix (Fin n) (Fin n) ℂ)) = {Y | ∃ X ∈ A, Y = E i * X} ∧ IsSimple (C i)) ∧
      (∀ X ∈ A, X = ∑ i, E i * X) := by sorry

end InvariantSDP.BlockDiag
