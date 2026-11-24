-- Prove2me | Theorems.Thm_LefebvreVariations_chains_sum_eq_mertens_sub_one
-- name    : LefebvreVariations.chains_sum_eq_mertens_sub_one
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-24T22:20:27.142556+00:00
-- url     : https://prove2.me/theorems/232fa87a-9de2-4adc-b065-a458483231cb
-- title:
--   Lefebvre's variations, No. 17 — on a theme by Riemann: signed divisibility chains count the Mertens function
-- statement:
--   This is the divisibility-chain form of the Mertens function.
--
--   For $N\ge1$, call a nonempty set $S\subseteq\{2,\dots,N\}$ a divisibility chain if any two of its elements, $a\le b$, satisfy $a\mid b$. Then
--
--   $$
--   \sum_{S}(-1)^{|S|}=M(N)-1,
--   $$
--
--   where the sum runs over all divisibility chains in $\{2,\dots,N\}$ and $M(N)=\sum_{n\le N}\mu(n)$ is the Mertens function.
--
--   The identity is an instance of Hall's theorem expressing the Möbius function of a poset as an alternating count of chains, applied to the divisibility order on $\{1,\dots,N\}$. It converts the Mertens-function criterion for the Riemann Hypothesis into a statement about signed counts of divisibility chains, and is unconditional.
-- source:
--   P. Hall, The Eulerian functions of a group, Quart. J. Math. 7 (1936), 134–151 (Möbius function of a poset as an alternating sum over chains), applied to the divisibility order; the divisibility-chain equivalent of the Riemann Hypothesis is in K. Broughan, Equivalents of the Riemann Hypothesis, Vol. 1, Cambridge Univ. Press, 2017. Parent problem: BroughanRH.divisibilityCycles.

import Mathlib

namespace LefebvreVariations

/-- Hall-type identity behind `BroughanRH.divisibilityCycles`: the signed count of nonempty
divisibility chains in `{2,…,N}` is `M(N) - 1`, where `M` is the Mertens function. -/
theorem chains_sum_eq_mertens_sub_one (N : ℕ) (hN : 1 ≤ N) :
    let chains (N : ℕ) := (Finset.Icc 2 N).powerset.filter fun S =>
      S.Nonempty ∧ ∀ a ∈ S, ∀ b ∈ S, a ≤ b → a ∣ b
    ∑ S ∈ chains N, (-1 : ℝ)^S.card =
      ∑ n ∈ Finset.Icc 1 N, (ArithmeticFunction.moebius n : ℝ) - 1 := by
  sorry

end LefebvreVariations
