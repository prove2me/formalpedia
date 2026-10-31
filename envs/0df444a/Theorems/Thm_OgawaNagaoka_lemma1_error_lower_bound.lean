-- Prove2me | Theorems.Thm_OgawaNagaoka_lemma1_error_lower_bound
-- name    : OgawaNagaoka.lemma1_error_lower_bound
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T15:23:26.541846+00:00
-- url     : https://prove2.me/theorems/83c8850d-17de-41a0-814a-26e0df009cca
-- title:
--   Lemma 1: $\mathrm{Pe}\ge1-\frac1M\mathrm{Tr}(\sum_k\rho_{u_k}^{1/\beta})^\beta$
-- statement:
--   Let $i\mapsto\rho_i$ be a classical-quantum channel (density operators on a finite-dimensional $H$). For every code with codebook $\{u_1,\dots,u_M\}\subset\mathcal X^n$, every measurement $X=\{X_k\}_{k=0}^M$ on $H^{\otimes n}$ and every $0<\beta\le1$,
--
--   $$
--   \mathrm{Pe}(\mathcal C,X)\ge1-\frac1M\,\mathrm{Tr}\Big(\sum_{k=1}^M\rho_{u_k}^{1/\beta}\Big)^\beta .
--   $$
--
--   The bound no longer depends on the decoder; it is the starting point of the random-coding argument that leads to Theorem 1.
--
--   Differences from the source:
--   - encoding: input alphabet $\mathcal X=\{1,\dots,a\}$, Hilbert space $H$ with $\dim H<\infty$, $H^{\otimes n}$ → finite types `A`, `D`; $H=\mathbb C^D$; $H^{\otimes n}=\mathbb C^{D^n}$ indexed by `Fin n → D`; reason: every finite alphabet and every finite-dimensional Hilbert space is isomorphic to such a model, so the instances are the same
--   - encoding: codebook $\{u_1,\dots,u_M\}\subset\mathcal X^n$ and decoder $\{X_0,X_1,\dots,X_M\}$ with $X_k\ge0$, $\sum_{k=0}^M X_k=I$ → `c : Fin M → (Fin n → A)` and a POVM `X : Option (Fin M) → Matrix _ _ ℂ` (`IsPOVM X`), `none` being the evasion outcome $X_0$; reason: literal transcription; codewords may repeat, as in the paper's list $u_1,\dots,u_M$
--   - encoding: a code has $M\ge1$ codewords (implicit; $1/M$ appears) → every `M : ℕ`; at `M = 0` Lean's `1/0 = 0` makes `Pe = 1`; reason: the added case $M=0$ is one where the source's expression is undefined, and the inequality holds there trivially
--   - encoding: traces $\mathrm{Tr}$ of operators → real part of the matrix trace; reason: the traces involved are traces of products of positive semidefinite operators or of Hermitian operators, which are real
--   - encoding: operator powers $B^p$ → `matPow B p = cfc (x ↦ x ^ p) B` (continuous functional calculus, `Real.rpow`); reason: for a positive semidefinite $B$ and $p>0$ the functional calculus is the definition of $B^p$, with $0^p=0$
--   - generalization: finite input alphabet $\mathcal X=\{1,\dots,a\}$ → an arbitrary type `A` (no `Fintype A`); reason: the bound involves only the $M$ codewords actually used, so the paper's finite-alphabet statement is the instance with `A` finite
-- source:
--   Ogawa–Nagaoka, Strong Converse to the Quantum Channel Coding Theorem, arXiv:quant-ph/9808063v2, Lemma 1, eq. (1), p.2

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_QAlgorithms_Defs_Ensemble
import Definitions.Def_OgawaNagaoka_matPow
import Definitions.Def_HolevoCQ_wordState
import Definitions.Def_OgawaNagaoka_avgError

open QAlgorithms

namespace OgawaNagaoka

/-- Ogawa–Nagaoka, *Strong Converse to the Quantum Channel Coding Theorem*,
arXiv:quant-ph/9808063v2, Lemma 1, eq. (1), p.2: for an arbitrary measurement
`X = {X_k}_{k=0}^M` and `0 < β ≤ 1`,
`Pe(C, X) ≥ 1 − (1/M) Tr (Σ_{k=1}^M ρ_{u_k}^{1/β})^β`.

**Formalization Note.** The channel is `i ↦ ρ i`, density matrices on `H = ℂ^D`; the codebook is
`c : Fin M → (Fin n → A)` (codewords may repeat) and the decoder is a POVM indexed by
`Option (Fin M)`, `none` being the evasion outcome `X₀`. The trace is its real part; powers are
`matPow`. At `M = 0` both sides are `1`. -/
theorem lemma1_error_lower_bound {A D : Type} [Fintype D] [DecidableEq D]
    (ρ : A → Matrix D D ℂ) (hρ : ∀ i, IsDensityMatrix (ρ i)) {n M : ℕ}
    (c : Fin M → (Fin n → A)) (X : Option (Fin M) → Matrix (Fin n → D) (Fin n → D) ℂ)
    (hX : IsPOVM X) (β : ℝ) (hβ0 : 0 < β) (hβ1 : β ≤ 1) :
    1 - (1 / (M : ℝ)) * (matPow (∑ k, matPow (HolevoCQ.wordState ρ n (c k)) (1 / β)) β).trace.re ≤
      avgError ρ c X := by sorry

end OgawaNagaoka
