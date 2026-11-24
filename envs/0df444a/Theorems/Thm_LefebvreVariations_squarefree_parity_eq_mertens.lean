-- Prove2me | Theorems.Thm_LefebvreVariations_squarefree_parity_eq_mertens
-- name    : LefebvreVariations.squarefree_parity_eq_mertens
-- status  : Open
-- author  : @Secousses
-- created : 2026-11-24T22:15:01.671463+00:00
-- url     : https://prove2.me/theorems/23cc8db8-330e-4ffe-8ee1-224580da40ef
-- title:
--   Lefebvre's variations, No. 14 — on a theme by Riemann: the squarefree parity surplus equals the Mertens function
-- statement:
--   This is the squarefree-parity form of the Mertens function.
--
--   For $N\ge0$, let $Q^+(N)$ and $Q^-(N)$ count the squarefree integers $1\le n\le N$ with an even, respectively odd, number of prime factors. Then
--
--   $$
--   Q^+(N)-Q^-(N)=\sum_{n=1}^{N}\mu(n)=M(N).
--   $$
--
--   This identity turns the Mertens-function criterion for the Riemann Hypothesis ($M(N)=O(N^{1/2+\varepsilon})$) into a statement about the balance between squarefree integers with an even and an odd number of prime factors. It is unconditional.
-- source:
--   Elementary consequence of the definition of the Möbius function (μ(n) = (−1)^ω(n) for squarefree n, μ(n) = 0 otherwise): G. H. Hardy and E. M. Wright, An Introduction to the Theory of Numbers, 6th ed., Oxford Univ. Press, 2008, §16.3; the squarefree-parity equivalent of the Riemann Hypothesis is in K. Broughan, Equivalents of the Riemann Hypothesis, Vol. 1, Cambridge Univ. Press, 2017. Parent problem: BroughanRH.squarefreeParity.

import Mathlib

namespace LefebvreVariations

/-- Identity behind `BroughanRH.squarefreeParity`: the surplus of squarefree integers with an even
number of prime factors over those with an odd number is exactly `M(N)`. -/
theorem squarefree_parity_eq_mertens (N : ℕ) :
    let pos (N : ℕ) := (Finset.Icc 1 N).filter fun n => Squarefree n ∧ Even n.primeFactors.card
    let neg (N : ℕ) := (Finset.Icc 1 N).filter fun n => Squarefree n ∧ Odd n.primeFactors.card
    ((pos N).card : ℝ) - ((neg N).card : ℝ) =
      ∑ n ∈ Finset.Icc 1 N, (ArithmeticFunction.moebius n : ℝ) := by
  sorry

end LefebvreVariations
