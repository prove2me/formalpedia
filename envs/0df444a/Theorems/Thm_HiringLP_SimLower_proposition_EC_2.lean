-- Prove2me | Theorems.Thm_HiringLP_SimLower_proposition_EC_2
-- name    : HiringLP.SimLower.proposition_EC_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T09:01:44.898752+00:00
-- url     : https://prove2.me/theorems/7becc008-68fd-497a-942d-3f7f14544b3e
-- title:
--   Proposition EC.2 — E(min{Pois(k), k}) = k(1 − e^{−k}k^k/k!)
-- statement:
--   For $k\in\mathbb N$, let $Z$ be a Poisson random variable with mean $k$. Then
--   $$\mathbb E(\min\{Z,k\})=k\Big(1-e^{-k}\frac{k^k}{k!}\Big).$$
--
--   This closed form turns the bound of Lemma 13 at $s=1$ into $1-e^{-k}k^k/(k!\,\tau)$.
--
--   **Formalization Note** Stated for every $k\in\mathbb N$, including $k=0$, where both sides are $0$ (with $0^0=1$).
-- source:
--   Epstein, Ma, Selection and Ordering Policies for Hiring Pipelines via Linear Programming, arXiv:2210.04059v3, p. ec3 (PDF p. 35), App. A.3, Proposition EC.2

import Mathlib
import Definitions.Def_HiringLP_SimLower_PoissonRatio

namespace HiringLP.SimLower

/-- Proposition EC.2 (p. ec3): for `Z ~ Pois(k)`, `E(min{Z, k}) = k (1 − e^{−k} kᵏ / k!)`. -/
theorem proposition_EC_2 (k : ℕ) :
    expMinPois k k = k * (1 - Real.exp (-(k : ℝ)) * (k : ℝ) ^ k / (k.factorial : ℝ)) := by sorry

end HiringLP.SimLower
