-- Prove2me | Theorems.Thm_HolevoCQ_eq_18
-- name    : HolevoCQ.eq_18
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T03:18:50.391161+00:00
-- url     : https://prove2.me/theorems/489978fb-5c51-4a77-ab9a-e3b858a8d53c
-- title:
--   Eq. (18): $\mathsf MP_{er}\le4\epsilon+(N-1)2^{-n[H(\bar S)-\bar H(S_{(\cdot)})-2\delta]}$
-- statement:
--   Let $\pi$ be a distribution on the finite alphabet $A$. Choose the code words $u_1,\dots,u_N$ independently with the product law (9) and decode with the rule (11) built from the typical projectors (6) and (8) with window parameter $\delta$. For every $\epsilon>0$ and $\delta>0$ there is $n_0=n(\pi,\epsilon,\delta)$ such that for all $n\ge n_0$ and every code size $N\ge1$
--
--   $$
--   \mathsf MP_{er}\le4\epsilon+(N-1)\,2^{-n[H(\bar S)-\bar H(S_{(\cdot)})-2\delta]},
--   $$
--
--   where $\bar S=\sum_i\pi_iS_i$ and $\bar H(S_{(\cdot)})=\sum_i\pi_iH(S_i)$. The threshold $n_0$ does not depend on $N$.
--
--   Differences from the source:
--   - encoding: input alphabet $A=\{1,\dots,a\}$, $D=\{1,\dots,d\}$, $\mathcal H=\mathbb C^d$, $\mathcal H^{\otimes n}$ → arbitrary finite types `A`, `D`; $\mathcal H=\mathbb C^D$; $\mathcal H^{\otimes n}=\mathbb C^{D^n}$ indexed by `Fin n → D`; reason: Lean convention; every finite alphabet is in bijection with some finite type and conversely, so the instances are the same
--   - encoding: the alphabet $A$ is not said to be nonempty → `[Nonempty A]`; reason: with $A$ empty there is no probability distribution on $A$, so $C_n$ and $\max_\pi$ are undefined; the hypothesis excludes only that undefined case
--   - generalization: "for fixed small positive $\epsilon,\delta$" → for every $\epsilon>0$ and $\delta>0$; reason: Lean covers every positive $\epsilon,\delta$, which contains the small ones the page has in mind
--   - encoding: expectation $\mathsf M$ over words drawn from the law (9) → finite sum over `u : Fin n → A` weighted by `wordProb π n u`; reason: the law (9) is a finite probability vector, so the expectation is this finite sum
--   - encoding: $P=\sum_{J\in B}|e_J\rangle\langle e_J|$, a sum over an eigenbasis with eigenvalue in the open window → `cfc` of the indicator of the open interval (`windowProj`); reason: for a Hermitian matrix this equals the sum of eigenprojectors with eigenvalue in the open window, for every choice of eigenbasis
--   - encoding: code size $N$ (implicitly $N\ge1$) → hypothesis `1 ≤ N`; reason: $1/N$ is undefined at $N=0$; the hypothesis excludes only that case
--   - encoding: the generalized inverse $X^{-1/2}$ of $X^{1/2}$ in (11) → `genInvSqrt`, `cfc` of $x\mapsto(\sqrt x)^{-1}$ with $(\sqrt0)^{-1}=0$ (inside `sqrtMeas`); reason: equal to $0$ on the kernel and $(X^{1/2})^{-1}$ on its orthogonal complement, the paper's definition
--   - encoding: traces $\mathrm{Tr}$ of operators → real part of the matrix trace; reason: the traces involved are real
-- source:
--   Holevo, The Capacity of Quantum Channel with General Signal States, arXiv:quant-ph/9611023v1, eq. (18), p.6

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_QAlgorithms_Defs_Ensemble
import Definitions.Def_HolevoCQ_avgState
import Definitions.Def_HolevoCQ_randomCodeError

open QAlgorithms

namespace HolevoCQ

/-- Holevo, *The Capacity of Quantum Channel with General Signal States*,
arXiv:quant-ph/9611023v1, eq. (18), p.6: when the words `u₁, …, u_N` are chosen independently with
the law (9) and decoded by (11), for `n ≥ n(π, ε, δ)`,
`M P_er ≤ 4ε + (N − 1) 2^{−n[H(S̄) − H̄(S(·)) − 2δ]}`.

**Formalization Note.** `n₀` depends on `π, ε, δ` only, not on `N`. `M P_er` is
`randomCodeError` (finite sum over codebooks). `H` is the binary `vnEntropy`, `2^x` is
`Real.rpow`. -/
theorem eq_18 {A D : Type} [Fintype A] [DecidableEq A] [Nonempty A] [Fintype D] [DecidableEq D]
    (S : A → Matrix D D ℂ) (hS : ∀ i, IsDensityMatrix (S i)) (π : A → ℝ)
    (hπ : π ∈ stdSimplex ℝ A) (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ N : ℕ, 1 ≤ N →
      randomCodeError S π n N δ ≤ 4 * ε + ((N : ℝ) - 1) *
        (2 : ℝ) ^ (-((n : ℝ) *
          (vnEntropy (avgState S π) - ∑ i, π i * vnEntropy (S i) - 2 * δ))) := by sorry

end HolevoCQ
