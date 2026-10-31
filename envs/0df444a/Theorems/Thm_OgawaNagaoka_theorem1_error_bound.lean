-- Prove2me | Theorems.Thm_OgawaNagaoka_theorem1_error_bound
-- name    : OgawaNagaoka.theorem1_error_bound
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T15:25:09.538403+00:00
-- url     : https://prove2.me/theorems/e1d3e617-7d38-4359-9b7a-3b97cd2903e6
-- title:
--   Theorem 1: $\mathrm{Pe}\ge1-\exp[-n(-sR+\min_\pi E_0(s,\pi))]$
-- statement:
--   Let $i\mapsto\rho_i$ be a classical-quantum channel with density operators on a finite-dimensional Hilbert space. For every code $(\mathcal C,X)$ with $M$ codewords of length $n$, rate $R=\log M/n$, and every $-1<s\le0$,
--
--   $$
--   \mathrm{Pe}(\mathcal C,X)\ge1-\exp\Big[-n\Big(-sR+\min_{\pi\in P_{\mathcal X}}E_0(s,\pi)\Big)\Big].
--   $$
--
--   This is the quantum analogue of Arimoto's lower bound: the error probability is bounded from below in terms of the rate and the single-letter function $E_0$ alone.
--
--   Differences from the source:
--   - encoding: input alphabet $\mathcal X=\{1,\dots,a\}$, Hilbert space $H$ with $\dim H<\infty$, $H^{\otimes n}$ → finite types `A`, `D`; $H=\mathbb C^D$; $H^{\otimes n}=\mathbb C^{D^n}$ indexed by `Fin n → D`; reason: every finite alphabet and every finite-dimensional Hilbert space is isomorphic to such a model, so the instances are the same
--   - encoding: codebook $\{u_1,\dots,u_M\}\subset\mathcal X^n$ and decoder $\{X_0,X_1,\dots,X_M\}$ with $X_k\ge0$, $\sum_{k=0}^M X_k=I$ → `c : Fin M → (Fin n → A)` and a POVM `X : Option (Fin M) → Matrix _ _ ℂ` (`IsPOVM X`), `none` being the evasion outcome $X_0$; reason: literal transcription; codewords may repeat, as in the paper's list $u_1,\dots,u_M$
--   - encoding: $R=\log M/n$ → `Real.log M / n` written out; natural logarithm; reason: at $n=0$ Lean's division gives $0$ and the bound reads $\mathrm{Pe}\ge0$, a case the paper does not consider and where the inequality is trivially true
--   - encoding: a code has $M\ge1$ codewords (implicit; $1/M$ appears) → every `M : ℕ`; at `M = 0` Lean's `1/0 = 0` makes `Pe = 1`; reason: the added case $M=0$ is one where the source's expression is undefined, and the inequality holds there trivially
--   - encoding: $\max$ / $\min$ over the probability distributions $P_{\mathcal X}$ (or $P_{\mathcal X^n}$) → real `sSup` / `sInf` of the image of `stdSimplex`; reason: the simplex is nonempty and compact for a nonempty alphabet and the function is continuous, so the supremum (infimum) is the attained maximum (minimum); with an empty alphabet the bound is vacuous or trivially true
--   - encoding: traces $\mathrm{Tr}$ of operators → real part of the matrix trace; reason: the traces involved are traces of products of positive semidefinite operators or of Hermitian operators, which are real
--   - encoding: operator powers $B^p$ → `matPow B p = cfc (x ↦ x ^ p) B` (continuous functional calculus, `Real.rpow`); reason: for a positive semidefinite $B$ and $p>0$ the functional calculus is the definition of $B^p$, with $0^p=0$
-- source:
--   Ogawa–Nagaoka, Strong Converse to the Quantum Channel Coding Theorem, arXiv:quant-ph/9808063v2, Theorem 1, eq. (12), p.6

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_QAlgorithms_Defs_Ensemble
import Definitions.Def_OgawaNagaoka_avgError
import Definitions.Def_OgawaNagaoka_E0

open QAlgorithms

namespace OgawaNagaoka

/-- Ogawa–Nagaoka, *Strong Converse to the Quantum Channel Coding Theorem*,
arXiv:quant-ph/9808063v2, Theorem 1, eq. (12), p.6: for all codes `(C, X)` and `−1 < s ≤ 0`,
`Pe(C, X) ≥ 1 − exp[−n[−sR + min_{π∈P_X} E₀(s, π)]]`, where `R = log M / n`.

**Formalization Note.** `R` is written out as `Real.log M / n` (natural logarithm). The minimum
over `π` is the real `sInf` of the image of the simplex under `E₀(s, ·)`: for a nonempty alphabet
and density matrices it is attained and finite. For `n = 0` (where `log M / 0 = 0` in Lean) or
`M = 0` the bound is trivially true; for an empty alphabet and `n ≥ 1` there is no codebook with
`M ≥ 1`. -/
theorem theorem1_error_bound {A D : Type} [Fintype A] [Fintype D] [DecidableEq D]
    (ρ : A → Matrix D D ℂ) (hρ : ∀ i, IsDensityMatrix (ρ i)) {n M : ℕ}
    (c : Fin M → (Fin n → A)) (X : Option (Fin M) → Matrix (Fin n → D) (Fin n → D) ℂ)
    (hX : IsPOVM X) (s : ℝ) (hs : s ∈ Set.Ioc (-1 : ℝ) 0) :
    1 - Real.exp (-((n : ℝ) * (-s * (Real.log M / n) + sInf (E0 ρ s '' stdSimplex ℝ A)))) ≤
      avgError ρ c X := by sorry

end OgawaNagaoka
