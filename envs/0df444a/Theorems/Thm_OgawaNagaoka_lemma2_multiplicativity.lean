-- Prove2me | Theorems.Thm_OgawaNagaoka_lemma2_multiplicativity
-- name    : OgawaNagaoka.lemma2_multiplicativity
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T15:24:17.655982+00:00
-- url     : https://prove2.me/theorems/8a9887d7-4877-42c1-8d35-52443cd47c25
-- title:
--   Lemma 2: $\max_P\mathrm{Tr}(\sum_uP(u)\rho_u^{1/\beta})^\beta=[\max_\pi\mathrm{Tr}(\sum_i\pi_i\rho_i^{1/\beta})^\beta]^n$
-- statement:
--   Let $P_{\mathcal X}$ be the set of probability distributions on the input alphabet $\mathcal X$ and $0<\beta\le1$. Then for every $n$,
--
--   $$
--   \max_{P\in P_{\mathcal X^n}}\mathrm{Tr}\Big(\sum_{u\in\mathcal X^n}P(u)\rho_u^{1/\beta}\Big)^\beta=\Big[\max_{\pi\in P_{\mathcal X}}\mathrm{Tr}\Big(\sum_{i=1}^a\pi_i\rho_i^{1/\beta}\Big)^\beta\Big]^n .
--   $$
--
--   Both maxima exist. The lemma reduces the $n$-letter bound (6) to a single-letter quantity, which makes the exponent of Theorem 1 independent of $n$.
--
--   Differences from the source:
--   - encoding: input alphabet $\mathcal X=\{1,\dots,a\}$, Hilbert space $H$ with $\dim H<\infty$, $H^{\otimes n}$ → finite types `A`, `D`; $H=\mathbb C^D$; $H^{\otimes n}=\mathbb C^{D^n}$ indexed by `Fin n → D`; reason: every finite alphabet and every finite-dimensional Hilbert space is isomorphic to such a model, so the instances are the same
--   - encoding: the alphabet $\mathcal X$ (not said to be nonempty) → `[Nonempty A]`; reason: with an empty alphabet $P_{\mathcal X}$ is empty and the maximum is undefined; the hypothesis excludes only that case
--   - reading: $\beta$ is not restricted in the statement → hypotheses `0 < β` and `β ≤ 1`; reason: the range of $\beta$ fixed in (1)–(6), where Lemma 2 is applied
--   - encoding: the identity of the two maxima → the single-letter maximum $v$ exists (`IsGreatest`), and every such $v$ has $v^n$ as the greatest value of the $n$-letter function; reason: states that both maxima are attained and equal, which is the content of an identity between maxima
--   - encoding: traces $\mathrm{Tr}$ of operators → real part of the matrix trace; reason: the traces involved are traces of products of positive semidefinite operators or of Hermitian operators, which are real
--   - encoding: operator powers $B^p$ → `matPow B p = cfc (x ↦ x ^ p) B` (continuous functional calculus, `Real.rpow`); reason: for a positive semidefinite $B$ and $p>0$ the functional calculus is the definition of $B^p$, with $0^p=0$
-- source:
--   Ogawa–Nagaoka, Strong Converse to the Quantum Channel Coding Theorem, arXiv:quant-ph/9808063v2, Lemma 2, p.4

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_HolevoCQ_wordState
import Definitions.Def_OgawaNagaoka_traceGallager

open QAlgorithms

namespace OgawaNagaoka

/-- Ogawa–Nagaoka, *Strong Converse to the Quantum Channel Coding Theorem*,
arXiv:quant-ph/9808063v2, Lemma 2, p.4: with `P_X` the set of probability distributions on `X`
and `0 < β ≤ 1`,
`max_{P∈P_{Xⁿ}} Tr (Σ_{u∈Xⁿ} P(u) ρ_u^{1/β})^β = [max_{π∈P_X} Tr (Σ_{i=1}^a π_i ρ_i^{1/β})^β]^n`.

**Formalization Note.** Both maxima are stated as attained (`IsGreatest`): the single-letter
maximum `v` exists, and every such `v` has `vⁿ` as the greatest value of the `n`-letter function
over the simplex on `Xⁿ = Fin n → A`. The alphabet is nonempty (otherwise `P_X` is empty and the
maximum is undefined). -/
theorem lemma2_multiplicativity {A D : Type} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype D] [DecidableEq D] (ρ : A → Matrix D D ℂ) (hρ : ∀ i, IsDensityMatrix (ρ i))
    (β : ℝ) (hβ0 : 0 < β) (hβ1 : β ≤ 1) (n : ℕ) :
    (∃ v, IsGreatest (traceGallager ρ β '' stdSimplex ℝ A) v) ∧
      ∀ v, IsGreatest (traceGallager ρ β '' stdSimplex ℝ A) v →
        IsGreatest (traceGallager (HolevoCQ.wordState ρ n) β '' stdSimplex ℝ (Fin n → A)) (v ^ n) := by sorry

end OgawaNagaoka
