-- Prove2me | Theorems.Thm_OgawaNagaoka_eq6_random_coding_bound
-- name    : OgawaNagaoka.eq6_random_coding_bound
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T15:24:14.136378+00:00
-- url     : https://prove2.me/theorems/3d4fe81b-b0eb-43ab-aac2-80aa0a4b956c
-- title:
--   Eqs. (3)–(6): $\min\mathrm{Pe}\ge1-M^{\beta-1}\max_P\mathrm{Tr}(\sum_uP(u)\rho_u^{1/\beta})^\beta$
-- statement:
--   For every block length $n$, every number of messages $M$ and every $0<\beta\le1$,
--
--   $$
--   \min_{\mathcal C,X}\mathrm{Pe}(\mathcal C,X)\ge1-M^{\beta-1}\max_{P\in P_{\mathcal X^n}}\mathrm{Tr}\Big(\sum_{u\in\mathcal X^n}P(u)\rho_u^{1/\beta}\Big)^\beta ,
--   $$
--
--   where the minimum is over all codes of cardinality $M$ and block length $n$, and $P_{\mathcal X^n}$ is the set of probability distributions on $\mathcal X^n$. The decoder and the codebook have been eliminated: the right side depends only on the channel, $n$, $M$ and $\beta$.
--
--   Differences from the source:
--   - encoding: input alphabet $\mathcal X=\{1,\dots,a\}$, Hilbert space $H$ with $\dim H<\infty$, $H^{\otimes n}$ → finite types `A`, `D`; $H=\mathbb C^D$; $H^{\otimes n}=\mathbb C^{D^n}$ indexed by `Fin n → D`; reason: every finite alphabet and every finite-dimensional Hilbert space is isomorphic to such a model, so the instances are the same
--   - encoding: codebook $\{u_1,\dots,u_M\}\subset\mathcal X^n$ and decoder $\{X_0,X_1,\dots,X_M\}$ with $X_k\ge0$, $\sum_{k=0}^M X_k=I$ → `c : Fin M → (Fin n → A)` and a POVM `X : Option (Fin M) → Matrix _ _ ℂ` (`IsPOVM X`), `none` being the evasion outcome $X_0$; reason: literal transcription; codewords may repeat, as in the paper's list $u_1,\dots,u_M$
--   - encoding: $\min_{\mathcal C,X}\mathrm{Pe}(\mathcal C,X)\ge\dots$ → `∀ c X, IsPOVM X → … ≤ avgError ρ c X`; reason: a lower bound on the minimum over all codes is the same as a lower bound on the error of every code
--   - encoding: a code has $M\ge1$ codewords (implicit; $1/M$ appears) → every `M : ℕ`; at `M = 0` Lean's `1/0 = 0` makes `Pe = 1`; reason: the added case $M=0$ is one where the source's expression is undefined, and the inequality holds there trivially
--   - encoding: $\max$ / $\min$ over the probability distributions $P_{\mathcal X}$ (or $P_{\mathcal X^n}$) → real `sSup` / `sInf` of the image of `stdSimplex`; reason: the simplex is nonempty and compact for a nonempty alphabet and the function is continuous, so the supremum (infimum) is the attained maximum (minimum); with an empty alphabet the bound is vacuous or trivially true
--   - encoding: traces $\mathrm{Tr}$ of operators → real part of the matrix trace; reason: the traces involved are traces of products of positive semidefinite operators or of Hermitian operators, which are real
--   - encoding: operator powers $B^p$ → `matPow B p = cfc (x ↦ x ^ p) B` (continuous functional calculus, `Real.rpow`); reason: for a positive semidefinite $B$ and $p>0$ the functional calculus is the definition of $B^p$, with $0^p=0$
-- source:
--   Ogawa–Nagaoka, Strong Converse to the Quantum Channel Coding Theorem, arXiv:quant-ph/9808063v2, eqs. (3)–(6), pp.3–4

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_QAlgorithms_Defs_Ensemble
import Definitions.Def_HolevoCQ_wordState
import Definitions.Def_OgawaNagaoka_avgError
import Definitions.Def_OgawaNagaoka_traceGallager

open QAlgorithms

namespace OgawaNagaoka

/-- Ogawa–Nagaoka, *Strong Converse to the Quantum Channel Coding Theorem*,
arXiv:quant-ph/9808063v2, eqs. (3)–(6), pp.3–4: for `0 < β ≤ 1`,
`min_{C,X} Pe(C, X) ≥ 1 − M^{β−1} max_{P∈P_{Xⁿ}} Tr (Σ_{u∈Xⁿ} P(u) ρ_u^{1/β})^β`.

**Formalization Note.** The bound on the minimum over codes is stated, equivalently, for every
code `(c, X)` of cardinality `M` and block length `n`. The maximum over the distributions `P` on
`Xⁿ = Fin n → A` is the real `sSup` of the image of the simplex `stdSimplex ℝ (Fin n → A)`
under `P ↦ traceGallager (HolevoCQ.wordState ρ n) β P = Tr (Σ_u P(u) ρ_u^{1/β})^β`; the set is nonempty
and compact when `A` is nonempty or `n = 0`, so the supremum is the maximum. `M^{β−1}` is
`Real.rpow`. -/
theorem eq6_random_coding_bound {A D : Type} [Fintype A] [DecidableEq A] [Fintype D]
    [DecidableEq D] (ρ : A → Matrix D D ℂ) (hρ : ∀ i, IsDensityMatrix (ρ i)) {n M : ℕ}
    (c : Fin M → (Fin n → A)) (X : Option (Fin M) → Matrix (Fin n → D) (Fin n → D) ℂ)
    (hX : IsPOVM X) (β : ℝ) (hβ0 : 0 < β) (hβ1 : β ≤ 1) :
    1 - (M : ℝ) ^ (β - 1) *
        sSup (traceGallager (HolevoCQ.wordState ρ n) β '' stdSimplex ℝ (Fin n → A)) ≤
      avgError ρ c X := by sorry

end OgawaNagaoka
