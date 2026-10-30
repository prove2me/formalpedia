-- Prove2me | Theorems.Thm_HolevoCQ_eq_7
-- name    : HolevoCQ.eq_7
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T03:16:45.032906+00:00
-- url     : https://prove2.me/theorems/17433c92-48ad-4ef3-b9d7-0d31c02b73ba
-- title:
--   Eq. (7): $\mathrm{Tr}\,\bar S^{\otimes n}(I-P)\le\epsilon$ for large $n$
-- statement:
--   Let $\pi$ be a distribution on the finite alphabet $A$, $\bar S=\sum_i\pi_iS_i$, and let $P$ be the typical projector (6) of $\bar S^{\otimes n}$ for the window parameter $\delta$. For every $\epsilon>0$ and $\delta>0$ there is $n_1=n_1(\pi,\epsilon,\delta)$ such that for all $n\ge n_1$
--
--   $$
--   \mathrm{Tr}\,\bar S^{\otimes n}(I-P)\le\epsilon .
--   $$
--
--   The typical subspace of $\bar S^{\otimes n}$ carries almost all of its weight; this is the quantum form of the asymptotic equipartition property.
--
--   Differences from the source:
--   - encoding: input alphabet $A=\{1,\dots,a\}$, $D=\{1,\dots,d\}$, $\mathcal H=\mathbb C^d$, $\mathcal H^{\otimes n}$ → arbitrary finite types `A`, `D`; $\mathcal H=\mathbb C^D$; $\mathcal H^{\otimes n}=\mathbb C^{D^n}$ indexed by `Fin n → D`; reason: Lean convention; every finite alphabet is in bijection with some finite type and conversely, so the instances are the same
--   - encoding: the alphabet $A$ is not said to be nonempty → `[Nonempty A]`; reason: with $A$ empty there is no probability distribution on $A$, so $C_n$ and $\max_\pi$ are undefined; the hypothesis excludes only that undefined case
--   - generalization: "for fixed small positive $\epsilon,\delta$" → for every $\epsilon>0$ and $\delta>0$; reason: Lean covers every positive $\epsilon,\delta$, which contains the small ones the page has in mind
--   - encoding: $P=\sum_{J\in B}|e_J\rangle\langle e_J|$, a sum over an eigenbasis with eigenvalue in the open window → `cfc` of the indicator of the open interval (`windowProj`); reason: for a Hermitian matrix this equals the sum of eigenprojectors with eigenvalue in the open window, for every choice of eigenbasis
--   - encoding: traces $\mathrm{Tr}$ of operators → real part of the matrix trace; reason: the traces involved are real
-- source:
--   Holevo, The Capacity of Quantum Channel with General Signal States, arXiv:quant-ph/9611023v1, eq. (7), p.3

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_HolevoCQ_tensorPowMat
import Definitions.Def_HolevoCQ_avgState
import Definitions.Def_HolevoCQ_typProj

open QAlgorithms

namespace HolevoCQ

/-- Holevo, *The Capacity of Quantum Channel with General Signal States*,
arXiv:quant-ph/9611023v1, eq. (7), p.3: for positive `ε, δ` and all `n ≥ n₁(π, ε, δ)`,
`Tr S̄^{⊗n}(I − P) ≤ ε`, where `S̄ = Σ_i π_i S_i` and `P` is the typical projector (6).

**Formalization Note.** Stated for every `ε > 0` and `δ > 0`. The trace is the real part
(the trace is real here). -/
theorem eq_7 {A D : Type} [Fintype A] [DecidableEq A] [Nonempty A] [Fintype D] [DecidableEq D]
    (S : A → Matrix D D ℂ) (hS : ∀ i, IsDensityMatrix (S i)) (π : A → ℝ)
    (hπ : π ∈ stdSimplex ℝ A) (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) :
    ∃ n₁ : ℕ, ∀ n ≥ n₁,
      (tensorPowMat (avgState S π) n * (1 - typProj S π n δ)).trace.re ≤ ε := by sorry

end HolevoCQ
