-- Prove2me | Theorems.Thm_LambdaCoalescent_Rates_consistent_of_succ
-- name    : LambdaCoalescent.Rates.consistent_of_succ
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:37:45.09108+00:00
-- url     : https://prove2.me/theorems/e4d75a7b-7531-4bba-95ec-63cab337d5e0
-- title:
--   Proof of Lemma 18 — adjacent restrictions suffice for consistency
-- statement:
--   Let $\lambda_{b,k}\ge 0$ for every $2\le k\le b$. Suppose that, for every $n$, every starting partition of $[n+1]$, every target partition of $[n]$, and every $t\ge0$, restricting the $(n+1)$-label chain gives the same time-$t$ transition probability as the $n$-label chain. Then the chains are consistent under every restriction $R_n$ from $[m]$ with $n<m$:
--
--   $$
--   R_n(\Pi_m)\mathrel{\overset{d}{=}}\Pi_n\quad(n<m),
--   $$
--
--   with the initial states related by restriction. This reduces the consistency check in Lemma 18 to adjacent sizes.
--
--   **Formalization Note** The hypothesis and conclusion use semigroup transition probabilities from every starting state. These determine the full finite-dimensional laws of the Markov chains.
-- source:
--   Pitman, Coalescents with multiple collisions, Ann. Probab. 27 (1999), p. 1882, proof of Lemma 18, “it suffices to consider m = n + 1”

import Definitions.Def_LambdaCoalescent_Rates_Setting

namespace LambdaCoalescent.Rates

open MeasureTheory

/-- Proof of Lemma 18, p. 1882: checking one added label suffices. -/
theorem consistent_of_succ (lam : ℕ → ℕ → ℝ)
    (hlam : ∀ b k, 2 ≤ k → k ≤ b → 0 ≤ lam b k)
    (hsucc : ∀ (n : ℕ) (π : Setoid (Fin (n + 1))) (σ : Setoid (Fin n))
      (t : ℝ), 0 ≤ t →
        (∑ π' : Setoid (Fin (n + 1)),
          if restrictLE (Nat.le_succ n) π' = σ then
            NormedSpace.exp (t • rateMatrix lam (n + 1)) π π' else 0) =
        NormedSpace.exp (t • rateMatrix lam n)
          (restrictLE (Nat.le_succ n) π) σ) :
    Consistent lam := by sorry

end LambdaCoalescent.Rates
