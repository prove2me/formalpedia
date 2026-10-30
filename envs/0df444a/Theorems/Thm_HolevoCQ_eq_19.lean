-- Prove2me | Theorems.Thm_HolevoCQ_eq_19
-- name    : HolevoCQ.eq_19
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T03:17:36.895013+00:00
-- url     : https://prove2.me/theorems/bbaa3867-c7ae-4980-894a-36d14098ac37
-- title:
--   Eq. (19): $p(n,N)\le4\epsilon+(N-1)2^{-n[\Delta H(\pi)-2\delta]}$
-- statement:
--   Let $\pi$ be a distribution on the finite alphabet $A$ and $\Delta H(\pi)=H(\sum_i\pi_iS_i)-\sum_i\pi_iH(S_i)$. For every $\epsilon>0$ and $\delta>0$ there is $n_0=n(\pi,\epsilon,\delta)$ such that for all $n\ge n_0$ and every $N\ge1$ the minimal average error probability of codes of size $N$ with words of length $n$ satisfies
--
--   $$
--   p(n,N)\le4\epsilon+(N-1)\,2^{-n[\Delta H(\pi)-2\delta]} .
--   $$
--
--   With $N=2^{n[\Delta H(\pi)-3\delta]}$ the right side tends to $4\epsilon$, which together with (4) gives $\Delta H(\pi)-3\delta\le C$.
--
--   Differences from the source:
--   - encoding: input alphabet $A=\{1,\dots,a\}$, $D=\{1,\dots,d\}$, $\mathcal H=\mathbb C^d$, $\mathcal H^{\otimes n}$ → arbitrary finite types `A`, `D`; $\mathcal H=\mathbb C^D$; $\mathcal H^{\otimes n}=\mathbb C^{D^n}$ indexed by `Fin n → D`; reason: Lean convention; every finite alphabet is in bijection with some finite type and conversely, so the instances are the same
--   - encoding: the alphabet $A$ is not said to be nonempty → `[Nonempty A]`; reason: with $A$ empty there is no probability distribution on $A$, so $C_n$ and $\max_\pi$ are undefined; the hypothesis excludes only that undefined case
--   - encoding: $p(n,N)$ is the minimum of $P_{er}$ over codes → real `sInf` of the set of error probabilities of codes; reason: the set is nonempty and bounded below by $0$, and the minimum is attained (compact set of codes), so `sInf` is the minimum
--   - generalization: "for fixed small positive $\epsilon,\delta$" → for every $\epsilon>0$ and $\delta>0$; reason: Lean covers every positive $\epsilon,\delta$, which contains the small ones the page has in mind
--   - generalization: $\pi=\pi^0$, the distribution maximizing $\Delta H$ → every distribution $\pi$ on $A$; reason: (18) gives the bound for every $\pi$; the maximizer is one case
--   - encoding: code size $N$ (implicitly $N\ge1$) → hypothesis `1 ≤ N`; reason: $1/N$ is undefined at $N=0$; the hypothesis excludes only that case
--   - encoding: traces $\mathrm{Tr}$ of operators → real part of the matrix trace; reason: the traces involved are real
-- source:
--   Holevo, The Capacity of Quantum Channel with General Signal States, arXiv:quant-ph/9611023v1, eq. (19), p.7

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_HolevoCQ_holevoChi
import Definitions.Def_HolevoCQ_minError

open QAlgorithms

namespace HolevoCQ

/-- Holevo, *The Capacity of Quantum Channel with General Signal States*,
arXiv:quant-ph/9611023v1, eq. (19), p.7: (18) implies
`p(n, N) ≤ 4ε + (N − 1) 2^{−n[ΔH(π) − 2δ]}` for `n ≥ n(π, ε, δ)`.

**Formalization Note.** The paper applies this to the maximizing distribution `π⁰`; it is stated
here for every distribution `π`, which contains that case. `n₀` depends on `π, ε, δ` only, not on
`N`. -/
theorem eq_19 {A D : Type} [Fintype A] [DecidableEq A] [Nonempty A] [Fintype D] [DecidableEq D]
    (S : A → Matrix D D ℂ) (hS : ∀ i, IsDensityMatrix (S i)) (π : A → ℝ)
    (hπ : π ∈ stdSimplex ℝ A) (ε δ : ℝ) (hε : 0 < ε) (hδ : 0 < δ) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ N : ℕ, 1 ≤ N →
      minError S n N ≤ 4 * ε + ((N : ℝ) - 1) *
        (2 : ℝ) ^ (-((n : ℝ) * (holevoChi S π - 2 * δ))) := by sorry

end HolevoCQ
