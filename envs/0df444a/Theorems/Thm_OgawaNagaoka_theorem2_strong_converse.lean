-- Prove2me | Theorems.Thm_OgawaNagaoka_theorem2_strong_converse
-- name    : OgawaNagaoka.theorem2_strong_converse
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T15:24:19.877983+00:00
-- url     : https://prove2.me/theorems/7819092a-82dc-41f5-af0b-d72bbcfbf056
-- title:
--   Theorem 2 (strong converse): above $C$, $\mathrm{Pe}\to1$ exponentially
-- statement:
--   Let $i\mapsto\rho_i$, $i\in\mathcal X$, be a classical-quantum channel with arbitrary density operators $\rho_i$ on a finite-dimensional Hilbert space $H$, and let $C=\max_\pi I(\pi)$. If $R>C$, then there is $r>0$ such that for every block length $n$, every number of messages $M\ge e^{nR}$, every codebook $\{u_1,\dots,u_M\}\subset\mathcal X^n$ and every decoding measurement $X=\{X_0,\dots,X_M\}$ on $H^{\otimes n}$,
--
--   $$
--   \mathrm{Pe}(\mathcal C,X)\ge1-e^{-nr}.
--   $$
--
--   In the paper's words: if $R>C$, then for all codes $\mathrm{Pe}(\mathcal C,X)$ goes to $1$ exponentially as $n\to\infty$. Decoders may be arbitrary (entangled) measurements on $H^{\otimes n}$, and the signal states may be mixed and non-commuting.
--
--   Differences from the source:
--   - encoding: input alphabet $\mathcal X=\{1,\dots,a\}$, Hilbert space $H$ with $\dim H<\infty$, $H^{\otimes n}$ → finite types `A`, `D`; $H=\mathbb C^D$; $H^{\otimes n}=\mathbb C^{D^n}$ indexed by `Fin n → D`; reason: every finite alphabet and every finite-dimensional Hilbert space is isomorphic to such a model, so the instances are the same
--   - encoding: codebook $\{u_1,\dots,u_M\}\subset\mathcal X^n$ and decoder $\{X_0,X_1,\dots,X_M\}$ with $X_k\ge0$, $\sum_{k=0}^M X_k=I$ → `c : Fin M → (Fin n → A)` and a POVM `X : Option (Fin M) → Matrix _ _ ℂ` (`IsPOVM X`), `none` being the evasion outcome $X_0$; reason: literal transcription; codewords may repeat, as in the paper's list $u_1,\dots,u_M$
--   - reading: $C$ (the operational capacity, p.2) → `holevoCap ρ` $=\max_\pi I(\pi)$; reason: the paper identifies $C$ with $\max_\pi I(\pi)$ by the quantum coding theorem, and its proof (Lemma 3 and the claim before Theorem 2) uses only $I(\pi)$
--   - generalization: $\mathrm{Pe}(\mathcal C,X)$ goes to $1$ exponentially as $n\to\infty$ for codes of rate $R$ → one $r>0$, fixed before $n$, with $\mathrm{Pe}\ge1-e^{-nr}$ for every $n$, every $M\ge e^{nR}$ and every code; reason: a uniform bound at every $n$ for all rates $\log M/n\ge R$ implies exponential convergence to $1$ for every sequence of codes of rate $R$
-- source:
--   Ogawa–Nagaoka, Strong Converse to the Quantum Channel Coding Theorem, arXiv:quant-ph/9808063v2, Theorem 2, p.9

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_QAlgorithms_Defs_Ensemble
import Definitions.Def_OgawaNagaoka_avgError
import Definitions.Def_OgawaNagaoka_holevoCap

open QAlgorithms

namespace OgawaNagaoka

/-- Ogawa–Nagaoka, *Strong Converse to the Quantum Channel Coding Theorem*,
arXiv:quant-ph/9808063v2, Theorem 2, p.9: if `R > C`, then for all codes `(C, X)`, `Pe(C, X)`
goes to `1` exponentially as `n → ∞`.

**Formalization Note.** `C` is `holevoCap ρ = max_π I(π)` (natural logarithm), which the paper
identifies with the operational capacity by the quantum coding theorem and which is the quantity
its proof uses. "Goes to 1 exponentially" is stated as an explicit bound with one exponent
`r > 0`, chosen before the block length: for every `n`, every `M ≥ e^{nR}` (rate `log M / n ≥ R`),
every codebook `c : Fin M → (Fin n → A)` (codewords may repeat) and every POVM decoder `X` indexed
by `Option (Fin M)` (`none` is the evasion outcome `X₀`), `Pe(c, X) ≥ 1 − e^{−nr}`. The channel is
an arbitrary family of density matrices `ρ_i` on `H = ℂ^D`; `H^{⊗n}` is `ℂ^{Fin n → D}`. -/
theorem theorem2_strong_converse {A D : Type} [Fintype A] [DecidableEq A] [Fintype D]
    [DecidableEq D] (ρ : A → Matrix D D ℂ) (hρ : ∀ i, IsDensityMatrix (ρ i)) (R : ℝ)
    (hR : holevoCap ρ < R) :
    ∃ r : ℝ, 0 < r ∧
      ∀ (n M : ℕ), Real.exp (n * R) ≤ M →
        ∀ (c : Fin M → (Fin n → A)) (X : Option (Fin M) → Matrix (Fin n → D) (Fin n → D) ℂ),
          IsPOVM X → 1 - Real.exp (-(n * r)) ≤ avgError ρ c X := by sorry

end OgawaNagaoka
