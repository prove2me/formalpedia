-- Prove2me | Theorems.Thm_OgawaNagaoka_traceGallager_concave
-- name    : OgawaNagaoka.traceGallager_concave
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T15:24:21.541894+00:00
-- url     : https://prove2.me/theorems/5d30e944-42dd-4613-a931-bb67b75ad7d1
-- title:
--   Proof of Lemma 2: $f(\pi)=\mathrm{Tr}(\sum_i\pi_i\rho_i^{1/\beta})^\beta$ is concave
-- statement:
--   Let $\rho_1,\dots,\rho_a$ be positive semidefinite operators on a finite-dimensional Hilbert space and $0<\beta\le1$. The function
--
--   $$
--   f(\pi)=\mathrm{Tr}\Big(\sum_{i=1}^a\pi_i\rho_i^{1/\beta}\Big)^\beta
--   $$
--
--   is concave on the set $P_{\mathcal X}$ of probability distributions $\pi$ on the alphabet. Concavity is what makes the conditions (7) sufficient for a maximum.
--
--   Differences from the source:
--   - generalization: density operators $\rho_i$ → positive semidefinite matrices $\rho_i$; reason: density operators are positive semidefinite, so the paper's statement is an instance
--   - reading: $0<\beta\le1$ is not repeated in the sentence → hypotheses `0 < β` and `β ≤ 1`; reason: the range of $\beta$ fixed in Lemma 1 and (3)–(6), on which Lemma 2 operates
--   - encoding: operator powers $B^p$ → `matPow B p = cfc (x ↦ x ^ p) B` (continuous functional calculus, `Real.rpow`); reason: for a positive semidefinite $B$ and $p>0$ the functional calculus is the definition of $B^p$, with $0^p=0$
--   - encoding: traces $\mathrm{Tr}$ of operators → real part of the matrix trace; reason: the traces involved are traces of products of positive semidefinite operators or of Hermitian operators, which are real
-- source:
--   Ogawa–Nagaoka, Strong Converse to the Quantum Channel Coding Theorem, arXiv:quant-ph/9808063v2, proof of Lemma 2, p.4

import Mathlib
import Definitions.Def_OgawaNagaoka_traceGallager

open scoped ComplexOrder

namespace OgawaNagaoka

/-- Ogawa–Nagaoka, *Strong Converse to the Quantum Channel Coding Theorem*,
arXiv:quant-ph/9808063v2, proof of Lemma 2, p.4: the function
`f(π) = Tr (Σ_{i=1}^a π_i ρ_i^{1/β})^β` of `π ∈ P_X` is concave (`0 < β ≤ 1`).

**Formalization Note.** The `ρ_i` are only assumed positive semidefinite (the paper's density
matrices are). Concavity is `ConcaveOn` on the simplex `stdSimplex ℝ A` of probability vectors. -/
theorem traceGallager_concave {A D : Type} [Fintype A] [Fintype D] [DecidableEq D]
    (ρ : A → Matrix D D ℂ) (hρ : ∀ i, (ρ i).PosSemidef) (β : ℝ) (hβ0 : 0 < β) (hβ1 : β ≤ 1) :
    ConcaveOn ℝ (stdSimplex ℝ A) (traceGallager ρ β) := by sorry

end OgawaNagaoka
