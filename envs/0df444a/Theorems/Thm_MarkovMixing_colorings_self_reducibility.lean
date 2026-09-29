-- Prove2me | Theorems.Thm_MarkovMixing_colorings_self_reducibility
-- name    : MarkovMixing.colorings_self_reducibility
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-22T23:31:55.099055+00:00
-- url     : https://prove2.me/theorems/25dd94c0-52a5-4a68-8ea7-47d5f5497273
-- title:
--   Theorem 14.12 -- self-reducibility of proper colorings
-- statement:
--   Let $G$ be a finite simple graph with vertex set $\{0,1,\dots,n-1\}$ and maximal degree $\Delta$, and let $q>2\Delta$ be a number of colours. A **proper colouring** assigns to each vertex one of the $q$ colours so that adjacent vertices differ; write $\Omega$ for the set of all proper colourings. Fix one proper colouring $x_0$, and for each $k$ let
--   $$\Omega_k=\{c\in\Omega:\ c(j)=x_0(j)\ \text{for every vertex } j\ge k\}$$
--   be the proper colourings whose last $n-k$ vertices are frozen to the values $x_0$ gives them, so that only the vertices $0,\dots,k-1$ are free.
--
--   The statement (the self-reducibility step inside the proof of Theorem 14.12 of Levin–Peres–Wilmer) asserts:
--
--   1. $|\Omega_0|=1$ — freezing every vertex leaves only $x_0$ itself;
--   2. every $\Omega_k$ is non-empty, and $\Omega_k\subseteq\Omega_{k+1}$ — releasing a vertex can only add colourings;
--   3. the reciprocal of the number of proper colourings is the telescoping product of the $n$ successive ratios,
--   $$\prod_{k=0}^{n-1}\frac{|\Omega_k|}{|\Omega_{k+1}|}=\frac{1}{|\Omega|};$$
--   4. for each $k<n$ the ratio is bounded away from $0$ and by $1$:
--   $$\frac{1}{q}\Bigl(1-\frac{\Delta}{q-\Delta}\Bigr)\;\le\;\frac{|\Omega_k|}{|\Omega_{k+1}|}\;\le\;1 .$$
--
--   This is the counting half of the sampling-to-counting reduction of Jerrum–Sinclair. Each factor $|\Omega_k|/|\Omega_{k+1}|$ is the probability that a uniformly random element of $\Omega_{k+1}$ happens to agree with $x_0$ at vertex $k$ — a quantity that the Glauber dynamics of this mission samples efficiently, since the frozen chain on $\Omega_{k+1}$ mixes under the same hypothesis $q>2\Delta$. Part (4) is what makes the estimation cheap: each factor is a probability of order $1/q$, so a number of samples polynomial in $n$, $q$ and the tolerance estimates it to within a small relative error, and part (3) then assembles the $n$ estimates into an estimate of $|\Omega|$ itself. Counting proper colourings exactly is $\#\mathsf P$-hard; this is the route to approximating the count in polynomial time.
--
--   *A note on the constant in (4).* LPW assert the cleaner bound $|\Omega_k|/|\Omega_{k+1}|\ge q^{-1}$, which is false. Take the four-cycle on $\{0,1,2,3\}$ with edges $02,\,03,\,12,\,13$, so $\Delta=2$; take $q=5>2\Delta$ and $x_0=(0,0,1,2)$, which is proper. Then $|\Omega_3|=52$ and $|\Omega_2|=9$, and $9/52<1/5$. The bound stated in (4) is what the argument actually gives: conditionally on the colours at all other vertices, the colour at a free vertex is uniform on the at least $q-\Delta$ colours its neighbours leave available, so no colour is taken with probability more than $(q-\Delta)^{-1}$; hence the colour $x_0(k)$ is unavailable to vertex $k$ only if one of its at most $\Delta$ free neighbours has taken it, an event of probability at most $\Delta/(q-\Delta)$, and when it is available it is taken with conditional probability at least $q^{-1}$. In LPW's proof the ratio bound serves only to bound the mean of each empirical estimator from below, so the correction rescales the number of samples per factor by $(1-\Delta/(q-\Delta))^{-1}$ and leaves Theorem 14.12 otherwise intact.
-- source:
--   D. A. Levin, Y. Peres, E. L. Wilmer, Markov Chains and Mixing Times, AMS 2009, https://documents.epfl.ch/groups/i/ip/ipg/www/2013-2014/Random_Walks/markovmixing.pdf, Section 14.4, proof of Theorem 14.12, Eq. (14.22)-(14.23), p. 196-197

import Definitions.Def_mm_transport

namespace MarkovMixing

/-- **Self-reducibility of proper colorings** (LPW, §14.4, inside the proof of
Theorem 14.12): fix a proper `q`-colouring `x₀` of a graph `G` on the vertex
set `Fin n` with maximal degree `Δ`, and for `k ≤ n` let `Ω k` be the proper
colourings that agree with `x₀` at every vertex `j ≥ k`, so that `Ω 0 = {x₀}`
and `Ω n = Ω` is the set of all proper colourings.  Then the reciprocal of the
number of proper colourings is the telescoping product of the `n` ratios
`|Ω k| / |Ω (k+1)|`, each of which lies in `[c(q,Δ)/q, 1]`, where
`c(q,Δ) = 1 − Δ/(q−Δ)` is positive for `q > 2Δ`.

This is the counting half of the sampling-to-counting reduction: each ratio is
the probability that a uniform element of `Ω (k+1)` agrees with `x₀` at vertex
`k`, which the mission's Glauber dynamics samples, and the bounds keep every
factor bounded away from `0` and `1` so that a fixed number of samples
suffices per factor.

*A note on the constant.*  LPW assert the sharper `|Ω k| / |Ω (k+1)| ≥ q⁻¹`,
which is false: for the four-cycle `v₁v₃v₂v₄` on `Fin 4`, `q = 5 > 2Δ = 4` and
`x₀ = (0,0,1,2)`, one has `|Ω 2| = 9` and `|Ω 3| = 52`, and `9/52 < 1/5`.  The
bound stated here is what the argument gives.  Conditionally on the colours
elsewhere, the colour at a free vertex is uniform on the at least `q − Δ`
colours its neighbours leave available, so no colour is taken with probability
more than `(q−Δ)⁻¹`; hence `x₀ k` is available to vertex `k` except on an event
of probability at most `Δ/(q−Δ)`, and when available it is taken with
conditional probability at least `q⁻¹`.  In LPW's proof the ratio bound serves
only to bound `E(W_k)` from below, so the correction rescales the sample count
`a_n` by `c(q,Δ)⁻¹` and leaves Theorem 14.12 otherwise intact. -/
theorem colorings_self_reducibility {n q : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (hq : 2 * G.maxDegree < q)
    (x₀ : Fin n → Fin q) (hx₀ : IsProperColoring G x₀)
    (Ω : ℕ → Finset (Fin n → Fin q))
    (hΩ : ∀ k : ℕ, Ω k = Finset.univ.filter fun c : Fin n → Fin q =>
      IsProperColoring G c ∧ ∀ j : Fin n, k ≤ (j : ℕ) → c j = x₀ j) :
    (Ω 0).card = 1 ∧
    (∀ k : ℕ, 0 < (Ω k).card) ∧
    (∀ k : ℕ, Ω k ⊆ Ω (k + 1)) ∧
    (∏ k ∈ Finset.range n, ((Ω k).card : ℝ) / ((Ω (k + 1)).card : ℝ)) =
      1 / ((Finset.univ.filter fun c : Fin n → Fin q =>
        IsProperColoring G c).card : ℝ) ∧
    (∀ k : ℕ, k < n →
      (1 - (G.maxDegree : ℝ) / ((q : ℝ) - G.maxDegree)) / (q : ℝ) ≤
          ((Ω k).card : ℝ) / ((Ω (k + 1)).card : ℝ) ∧
        ((Ω k).card : ℝ) / ((Ω (k + 1)).card : ℝ) ≤ 1) := by
  sorry

end MarkovMixing
