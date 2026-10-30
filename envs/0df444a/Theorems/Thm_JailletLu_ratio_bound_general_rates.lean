-- Prove2me | Theorems.Thm_JailletLu_ratio_bound_general_rates
-- name    : JailletLu.ratio_bound_general_rates
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T01:34:46.21964+00:00
-- url     : https://prove2.me/theorems/9c77a81e-4173-4823-af47-c6f0a649e1d8
-- title:
--   Section 5.4: the per-advertiser ratio bound is at least 0.706 (corrected: $n\ge 311$)
-- statement:
--   **Setting.** Let $A$ (advertisers) and $I$ (impression types) be finite sets, $E\subseteq A\times I$ the edges of the bipartite graph ($a\sim i$ when $(a,i)\in E$), $r_i\le 1$ the arrival rate of type $i$ (the standing assumption of §5), and $n$ the number of requests. Let $f=(f_{a,i})$ be a feasible point of LP (4), extended by the dummy advertiser $a_d$ with $f_{a_d,i}=r_i-\sum_{a}f_{a,i}$ and the convention $f_{a_d}=1$, and write $f_a=\sum_{i\sim a}f_{a,i}$. Fix, for every type $i$, any order $a_1,\dots,a_k$ of the advertisers interested in $i$ (the dummy included). The list numbers $m^i_{b,c}$ and $m_{b,c}=\sum_i m^i_{b,c}$ ($b,c\in A^*=A\cup\{a_d\}$) are those of the §5.3 construction, and for $a\in A$: $A^*_a=A^*\setminus\{a\}$, $\beta_a=\max_{a_1\in A^*_a}m_{a,a_1}$, $s_a=\sum_{a_1\in A^*_a}m_{a,a_1}$.
--
--   Then for every $n\ge 311$ and every advertiser $a\in A$ with $f_a>0$,
--   $$
--   \frac1{f_a}\Big(1-e^{-f_a}+\frac1e\sum_{a_1\in A^*_a}g(f_a,m_{a,a_1})-\frac1{2e}\Big(\sum_{a_1\in A^*_a}g(f_{a_1},m_{a_1,a})\Big)^2+\frac1{2e}\sum_{a_1\in A^*_a}g(f_a,m_{a,a_1})^2\Big)\ \ge\ 0.706 .
--   $$
--   The left side is the third line of the competitive-ratio chain of §5.4 (the minimum over $a$ in the paper), and the paper concludes "Theorem 3 follows from Claim 4": the random-lists algorithm for general arrival rates matches each advertiser with probability at least $0.706\,f_a$. The numbers $m$, $\beta_a$, $s_a$ are computed from $f$ by the list construction; the constraints of Claim 4 are consequences, not hypotheses.
--
--   The paper states the range "for $n\ge 100$", which is false. Take advertisers $a,a_1$, types $i_1,i_2,i_3$, $\sigma=\ln 2-\tfrac1n$, rates $r=(1,\sigma,1-\sigma)$, flows $f_{a,\cdot}=(1-\sigma/2,\ \sigma/2,\ 0)$ and $f_{a_1,\cdot}=(\sigma/2,\ \sigma/2,\ 1-\sigma)$, orders $a,a_1,a_d$. This $f$ is feasible (indeed optimal) for (4), $m_{a,a_1}=\sigma$, $m_{a,a_d}=0$, and the ratio of $a$ is $1-e^{-1}+e^{-1}g(1,\sigma)$: $\approx 0.705433$ at $n=100$, $\approx 0.7059993$ at $n=310$ and $\approx 0.7060002$ at $n=311$. So $311$ is sharp. The paper's chain (the reduction to $R$ plus Claim 4) proves the bound for $n\ge 2929$; for $311\le n\le 2928$ it holds numerically but no lemma of the paper covers it.
--
--   Differences from the source:
--   - reading: the order a_1, …, a_k of the advertisers interested in i is not fixed → every admissible order: a duplicate-free list of exactly the interested advertisers, dummy included; reason: the paper fixes no order; the statement holds for every one
--   - reading: x ± r_i/2 ∈ [Σ_{l<k} f_{a_l,i}, Σ_{l≤k} f_{a_l,i}] → rot(x) = x + r_i/2 if x < r_i/2, else x − r_i/2, with closed intervals; reason: for x ∈ [0, r_i] this is the one of x ± r_i/2 lying in [0, r_i] (both only at x = r_i/2); interval endpoints have measure 0
--   - encoding: m^i_{b,c}, the expected number of requests of type i whose list is ⟨b, c⟩ → Lebesgue measure of {x ∈ [0, r_i] : x ∈ J_i(b), rot(x) ∈ J_i(c)}; reason: n requests, type i with probability r_i/n, x uniform on [0, r_i]: n · (r_i/n) · |·|/r_i = |·|; same values, the probability space is not built
--   - generalization: f the solution of LP (4) used by the algorithm, with Σ_i r_i = n → f any feasible point of LP (4); Σ_i r_i = n not assumed; reason: optimality and the normalization are never used; the paper's f is feasible, so the statement specializes to it
--   - reading: "Theorem 3 follows from Claim 4" through the chain on p. 15 → the third line of the chain is at least 0.706; reason: lines 1–2 of the chain rest on asymptotic independence (proof omitted in the paper); the third line onward is the exact algebraic part of Theorem 3
--   - correction: for n ≥ 100 → for n ≥ 311; reason: false at n = 100: the instance above (feasible, even optimal, for (4), r_i ≤ 1) has ratio ≈ 0.705433 < 0.706; it stays below 0.706 up to n = 310 (≈ 0.7059993) and reaches ≈ 0.7060002 at n = 311 (planning_numerics/check_claim4.py)
--   - encoding: min_{a∈A} [ … ] / f_a ≥ 0.706 → for every a with f_a > 0, [ … ] / f_a ≥ 0.706; reason: equivalent wherever the minimum of the printed quotients is defined (A nonempty, f_a > 0)
-- source:
--   Jaillet and Lu, Online Stochastic Matching: New Algorithms with Better Bounds, accepted manuscript (revised June 2013) of Mathematics of Operations Research (2014), doi:10.1287/moor.2013.0621, §5.4, p. 15, third line of the chain; p. 16, Claim 4 and "Theorem 3 follows from Claim 4"

import Mathlib
import Definitions.Def_JailletLu_LP4Feasible
import Definitions.Def_JailletLu_IsAdmissibleOrder
import Definitions.Def_JailletLu_fTot
import Definitions.Def_JailletLu_third

namespace JailletLu

/-- **Section 5.4: the per-advertiser ratio bound is at least 0.706 (corrected: n ≥ 311).**
Jaillet and Lu, *Online Stochastic Matching: New Algorithms with Better Bounds*, accepted
manuscript (revised June 2013) of Mathematics of Operations Research (2014), doi:10.1287/moor.2013.0621, §5.4, p. 15, third line of the chain:
"≥ min_{a∈A} [1 − e^{−f_a} + (1/e) Σ_{a1∈A*_a} g(f_a, m_{a,a1}) − (1/(2e)) (Σ_{a1∈A*_a} g(f_{a1}, m_{a1,a}))²
+ (1/(2e)) Σ_{a1∈A*_a} g(f_a, m_{a,a1})²] / f_a", and p. 16: "We can numerically show that, for
n ≥ 100: Claim 4. … R(f_a, β_a, s_a) ≥ 0.706." "Theorem 3 follows from Claim 4."

Setting (§5, p. 12 and §5.3, p. 13): `r_i ≤ 1` for every type (the standing assumption of §5), `f`
feasible for LP (4) with parameter `n`, and an admissible order of the interested advertisers for
every type (any order: the paper fixes none). The list numbers are those of the §5.3 construction.
Conclusion: for every `n ≥ 311` and every advertiser `a` with `f_a > 0`, the third-line ratio
`third_a / f_a` is at least `0.706`. The list numbers `m`, `β_a`, `s_a` and `f_{a_d} = 1` are
computed from `f` by the §5.3 construction; none of the constraints of Claim 4 is assumed.

**Formalization Note.** *Correction.* The printed range `n ≥ 100` is false: take advertisers
`a, a1`, types `i1, i2, i3`, `σ = ln 2 − 1/n`, `r = (1, σ, 1 − σ)`, `f_{a,·} = (1 − σ/2, σ/2, 0)`,
`f_{a1,·} = (σ/2, σ/2, 1 − σ)`, orders `a, a1, a_d`. This `f` is feasible (even optimal) for (4),
`m_{a,a1} = σ`, `m_{a,a_d} = 0`, and the ratio of `a` is `1 − 1/e + g(1, σ)/e`: `≈ 0.705433` at
`n = 100`, `≈ 0.7059993` at `n = 310`, `≈ 0.7060002` at `n = 311`. So `311` is sharp. *Proof route.*
The paper's chain (`third_ge_R` with Claim 4) gives the bound only for `n ≥ 2929`; for
`311 ≤ n ≤ 2928` the bound is true numerically (the single-neighbour configuration above is extremal)
but no lemma of the paper covers that range. *Encoding.* `∀ a, 0 < f_a → …` replaces `min_{a∈A}`;
they agree wherever the printed quotient is defined. -/
theorem ratio_bound_general_rates {A I : Type*} [Fintype A] [Fintype I] [DecidableEq A]
    (E : Set (A × I)) (r : I → ℝ) (hr : ∀ i, r i ≤ 1) (n : ℕ) (f : A → I → ℝ)
    (hf : LP4Feasible E r n f) (ord : I → List (Option A)) (hord : IsAdmissibleOrder E ord) (hn : 311 ≤ n) :
    ∀ a : A, 0 < fTot f a → (0.706 : ℝ) ≤ third r f ord a / fTot f a := by sorry

end JailletLu
