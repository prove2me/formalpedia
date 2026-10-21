-- Prove2me | Theorems.Thm_HiringLP_SimUpper_ec15_chain
-- name    : HiringLP.SimUpper.ec15_chain
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T10:59:31.89425+00:00
-- url     : https://prove2.me/theorems/6cf32fe5-a630-467f-b654-1abb757de2eb
-- title:
--   (EC.15), p. ec19 — offering to m ≤ j² type-1 candidates earns (τ+δ)km/j + E min{0, k − Bin(m, k/j)} ≤ k + (km/j)(τ + δ − P(A_j))
-- statement:
--   Let $1 \le k \le j$ be integers, $\varepsilon > 0$, $\tau \in (0,1)$, $\delta = \varepsilon\tau/j$, and let $I$ be the hard instance ($j^2$ type-1 candidates with $p_i = k/j$, $v_i = \tau + \delta$, then $k$ type-2 candidates with $p_i = 1$, $v_i = \tau$). Let $0 \le m \le j^2$, so the value-ordered policy with parameter $m$ offers only to $m$ type-1 candidates, and let $B \sim \mathrm{Bin}(m, k/j)$ be the number of acceptances. Then its expected reward $\mathrm{ALG}$ satisfies
--   $$
--   \mathrm{ALG} = (\tau + \delta)\,\frac{km}{j} + \mathbb{E}[\min\{0, k - B\}]
--   $$
--   and
--   $$
--   \mathrm{ALG} \le k + \frac{km}{j}\bigl(\tau + \delta - \Pr[B > k]\bigr).
--   $$
--
--   The identity rewrites the model's reward in Binomial terms; the inequality shows that if $m/j \to \infty$ the reward tends to $-\infty$, which is how the proof restricts attention to $m = O(j)$.
-- source:
--   Epstein, Ma, Selection and Ordering Policies for Hiring Pipelines via Linear Programming, arXiv:2210.04059v3, App. D.7, p. ec19 (PDF p. 51), display (EC.15) and the chain following it

import Mathlib
import Definitions.Def_HiringLP_SimUpper_Model
import Definitions.Def_HiringLP_SimUpper_HardInstance
import Definitions.Def_HiringLP_SimUpper_Binomial

namespace HiringLP.SimUpper

open Finset

/-- App. D.7, (EC.15), p. ec19: on the hard instance, the value-ordered policy that offers to
`m ≤ j²` candidates (all of type 1) earns
`(τ + δ) k m / j + E[min{0, k − Bin(m, k/j)}]`, with `δ = ετ/j`, and this is at most
`k + (k m / j)(τ + δ − P(Bin(m, k/j) > k))`. -/
theorem ec15_chain (k j m : ℕ) (ε τ : ℝ) (hk : 1 ≤ k) (hkj : k ≤ j) (hε : 0 < ε)
    (hτ0 : 0 < τ) (hτ1 : τ < 1) (hm : m ≤ j ^ 2) :
    reward (hardInstance k j ε τ) (valueOrdered m) =
        (τ + ε * τ / j) * k * m / j +
          ∑ t ∈ range (m + 1), binomPMF m ((k : ℝ) / j) t * min 0 ((k : ℝ) - t) ∧
    reward (hardInstance k j ε τ) (valueOrdered m) ≤
        k + k * m / j * (τ + ε * τ / j - tailBinom m ((k : ℝ) / j) k) := by sorry

end HiringLP.SimUpper
