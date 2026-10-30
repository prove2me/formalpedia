-- Prove2me | Theorems.Thm_HolevoCQ_eq_10
-- name    : HolevoCQ.eq_10
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T03:17:15.587603+00:00
-- url     : https://prove2.me/theorems/4f096fcc-623a-4d36-a7d5-bc3ef3824100
-- title:
--   Eq. (10): $\mathsf M\,\mathrm{Tr}\,S_u(I-P_u)\le\epsilon$ for large $n$
-- statement:
--   Let $\pi$ be a distribution on the finite alphabet $A$, let the word $u\in A^n$ be drawn from the product law (9), and let $P_u$ be the typical projector (8) of $S_u$ for the window parameter $\delta$. For every $\epsilon>0$ and $\delta>0$ there is $n_2=n_2(\pi,\epsilon,\delta)$ such that for all $n\ge n_2$
--
--   $$
--   \mathsf M\,\mathrm{Tr}\,S_u(I-P_u)\le\epsilon .
--   $$
--
--   On average over the random word, the conditionally typical subspace of $S_u$ carries almost all of its weight.
--
--   Differences from the source:
--   - encoding: input alphabet $A=\{1,\dots,a\}$, $D=\{1,\dots,d\}$, $\mathcal H=\mathbb C^d$, $\mathcal H^{\otimes n}$ → arbitrary finite types `A`, `D`; $\mathcal H=\mathbb C^D$; $\mathcal H^{\otimes n}=\mathbb C^{D^n}$ indexed by `Fin n → D`; reason: Lean convention; every finite alphabet is in bijection with some finite type and conversely, so the instances are the same
--   - encoding: the alphabet $A$ is not said to be nonempty → `[Nonempty A]`; reason: with $A$ empty there is no probability distribution on $A$, so $C_n$ and $\max_\pi$ are undefined; the hypothesis excludes only that undefined case
--   - generalization: "for fixed small positive $\epsilon,\delta$" → for every $\epsilon>0$ and $\delta>0$; reason: Lean covers every positive $\epsilon,\delta$, which contains the small ones the page has in mind
--   - encoding: $P=\sum_{J\in B}|e_J\rangle\langle e_J|$, a sum over an eigenbasis with eigenvalue in the open window → `cfc` of the indicator of the open interval (`windowProj`); reason: for a Hermitian matrix this equals the sum of eigenprojectors with eigenvalue in the open window, for every choice of eigenbasis
--   - encoding: traces $\mathrm{Tr}$ of operators → real part of the matrix trace; reason: the traces involved are real
--   - encoding: expectation $\mathsf M$ over words drawn from the law (9) → finite sum over `u : Fin n → A` weighted by `wordProb π n u`; reason: the law (9) is a finite probability vector, so the expectation is this finite sum
-- source:
--   Holevo, The Capacity of Quantum Channel with General Signal States, arXiv:quant-ph/9611023v1, eq. (10), p.4

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_HolevoCQ_wordState
import Definitions.Def_HolevoCQ_wordProb
import Definitions.Def_HolevoCQ_condTypProj

open QAlgorithms

namespace HolevoCQ

/-- Holevo, *The Capacity of Quantum Channel with General Signal States*,
arXiv:quant-ph/9611023v1, eq. (10), p.4: with words `u` drawn from the product law (9), for
positive `ε, δ` and all `n ≥ n₂(π, ε, δ)`, `M Tr S_u(I − P_u) ≤ ε`, where `P_u` is the typical
projector (8) of `S_u`.

**Formalization Note.** The expectation `M` is the finite sum over `u : Fin n → A` weighted by
`wordProb π n u`. Stated for every `ε > 0` and `δ > 0`. -/
theorem eq_10 {A D : Type} [Fintype A] [DecidableEq A] [Nonempty A] [Fintype D] [DecidableEq D]
    (S : A → Matrix D D ℂ) (hS : ∀ i, IsDensityMatrix (S i)) (π : A → ℝ)
    (hπ : π ∈ stdSimplex ℝ A) (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) :
    ∃ n₂ : ℕ, ∀ n ≥ n₂,
      ∑ u : Fin n → A, wordProb π n u *
        (wordState S n u * (1 - condTypProj S π n δ u)).trace.re ≤ ε := by sorry

end HolevoCQ
