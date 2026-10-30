-- Prove2me | Theorems.Thm_HolevoCQ_eq_4
-- name    : HolevoCQ.eq_4
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T03:18:59.492065+00:00
-- url     : https://prove2.me/theorems/16ba1ca4-592e-497a-82eb-c33056e3c095
-- title:
--   Eq. (4): $p(n,2^{n(C-\delta)})\to0$ and $p(n,2^{n(C+\delta)})\not\to0$
-- statement:
--   Let $C$ be the capacity (3) of the classical-quantum channel $i\mapsto S_i$ and $p(n,N)$ the minimal average error probability over codes of size $N$ with words of length $n$. Then for every $\delta>0$, as $n\to\infty$,
--
--   $$
--   p\big(n,2^{n(C-\delta)}\big)\to0\qquad\text{and}\qquad p\big(n,2^{n(C+\delta)}\big)\not\to0 .
--   $$
--
--   This is the operational meaning of $C$: rates below $C$ are achievable with vanishing error and rates above $C$ are not.
--
--   Differences from the source:
--   - encoding: input alphabet $A=\{1,\dots,a\}$, $D=\{1,\dots,d\}$, $\mathcal H=\mathbb C^d$, $\mathcal H^{\otimes n}$ → arbitrary finite types `A`, `D`; $\mathcal H=\mathbb C^D$; $\mathcal H^{\otimes n}=\mathbb C^{D^n}$ indexed by `Fin n → D`; reason: Lean convention; every finite alphabet is in bijection with some finite type and conversely, so the instances are the same
--   - encoding: the alphabet $A$ is not said to be nonempty → `[Nonempty A]`; reason: with $A$ empty there is no probability distribution on $A$, so $C_n$ and $\max_\pi$ are undefined; the hypothesis excludes only that undefined case
--   - encoding: $p(n,N)$ is the minimum of $P_{er}$ over codes → real `sInf` of the set of error probabilities of codes; reason: the set is nonempty and bounded below by $0$, and the minimum is attained (compact set of codes), so `sInf` is the minimum
--   - reading: a code of size $N$ is printed as "$(u_1,X_1),\dots,(u_n,X_n)$" → a code is indexed by `Fin N`; reason: the code has size $N$ ($\sum_{j=1}^N$) and $n$ is the word length, so the printed $n$ is a typo for $N$
--   - reading: code size $2^{n(C\mp\delta)}$, not an integer in general → $\lceil 2^{n(C-\delta)}\rceil$ in the first claim, $\lfloor 2^{n(C+\delta)}\rfloor$ in the second; reason: $p(n,N)$ is nondecreasing in $N$, so rounding up in the first claim and down in the second gives the stronger statement
--   - encoding: traces $\mathrm{Tr}$ of operators → real part of the matrix trace; reason: the traces involved are real
-- source:
--   Holevo, The Capacity of Quantum Channel with General Signal States, arXiv:quant-ph/9611023v1, eq. (4), p.2

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Information
import Definitions.Def_HolevoCQ_capacity
import Definitions.Def_HolevoCQ_minError

open Filter Topology QAlgorithms

namespace HolevoCQ

/-- Holevo, *The Capacity of Quantum Channel with General Signal States*,
arXiv:quant-ph/9611023v1, eq. (4), p.2: for every `δ > 0`, as `n → ∞`,
`p(n, 2^{n(C−δ)}) → 0` and `p(n, 2^{n(C+δ)}) ↛ 0`, where `p(n, N)` is the minimal average error
probability of codes of size `N` with words of length `n` and `C` is the capacity (3).

**Formalization Note.** The code size `2^{n(C∓δ)}` is rounded up (`⌈·⌉₊`) in the first claim and
down (`⌊·⌋₊`) in the second; since `p(n, N)` is nondecreasing in `N`, these are the stronger
readings. Both halves of (4) are stated. -/
theorem eq_4 {A D : Type} [Fintype A] [DecidableEq A] [Nonempty A] [Fintype D] [DecidableEq D]
    (S : A → Matrix D D ℂ) (hS : ∀ i, IsDensityMatrix (S i)) (δ : ℝ) (hδ : 0 < δ) :
    Tendsto (fun n : ℕ => minError S n ⌈(2 : ℝ) ^ ((n : ℝ) * (capacity S - δ))⌉₊) atTop (𝓝 0) ∧
      ¬ Tendsto (fun n : ℕ => minError S n ⌊(2 : ℝ) ^ ((n : ℝ) * (capacity S + δ))⌋₊) atTop
        (𝓝 0) := by sorry

end HolevoCQ
