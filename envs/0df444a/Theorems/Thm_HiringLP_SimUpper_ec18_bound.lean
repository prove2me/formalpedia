-- Prove2me | Theorems.Thm_HiringLP_SimUpper_ec18_bound
-- name    : HiringLP.SimUpper.ec18_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T10:59:35.170692+00:00
-- url     : https://prove2.me/theorems/e5868bc4-37bc-414f-a491-e4959974bce3
-- title:
--   (EC.18), p. ec20 — offering to m ≤ j² type-1 candidates earns at most εkτ + (km/j)(τ − 1) + E min{k, Bin(m, k/j)}
-- statement:
--   Let $1 \le k \le j$ be integers, $\varepsilon > 0$, $\tau \in (0,1)$, and let $I$ be the hard instance ($j^2$ type-1 candidates with $p_i = k/j$, $v_i = \tau + \varepsilon\tau/j$, then $k$ type-2 candidates with $p_i = 1$, $v_i = \tau$). Let $0 \le m \le j^2$ and $B \sim \mathrm{Bin}(m, k/j)$. The expected reward $\mathrm{ALG}$ of the value-ordered policy with parameter $m$ equals (EC.17)
--   $$
--   \mathrm{ALG} = \tau\frac{mk}{j} + \frac{\varepsilon k \tau m}{j^2} - \frac{mk}{j} + \mathbb{E}[\min\{k, B\}],
--   $$
--   and therefore (EC.18)
--   $$
--   \mathrm{ALG} \le \varepsilon k \tau + \frac{km}{j}(\tau - 1) + \mathbb{E}[\min\{k, B\}].
--   $$
--
--   Dividing by $\mathrm{OPT}_{\mathrm{sim}}(I) \ge k\tau$ and letting $j \to \infty$ with $m/j \to s$ (so that $B$ approaches $\mathrm{Pois}(sk)$) gives the objective $\varepsilon + s - s/\tau + \mathbb{E}[\min\{\mathrm{Pois}(sk), k\}]/(k\tau)$ whose supremum is $\beta^\tau_k + \varepsilon$.
-- source:
--   Epstein, Ma, Selection and Ordering Policies for Hiring Pipelines via Linear Programming, arXiv:2210.04059v3, App. D.7, p. ec20 (PDF p. 52), displays (EC.16)–(EC.18)

import Mathlib
import Definitions.Def_HiringLP_SimUpper_Model
import Definitions.Def_HiringLP_SimUpper_HardInstance
import Definitions.Def_HiringLP_SimUpper_Binomial

namespace HiringLP.SimUpper

/-- App. D.7, (EC.16)–(EC.18), p. ec20: on the hard instance, the value-ordered policy that offers
to `m ≤ j²` candidates (all of type 1) earns exactly
`τ m k / j + ε k τ m / j² − m k / j + E[min{k, Bin(m, k/j)}]` (EC.17), which is at most
`ε k τ + (k m / j)(τ − 1) + E[min{k, Bin(m, k/j)}]` (EC.18). -/
theorem ec18_bound (k j m : ℕ) (ε τ : ℝ) (hk : 1 ≤ k) (hkj : k ≤ j) (hε : 0 < ε)
    (hτ0 : 0 < τ) (hτ1 : τ < 1) (hm : m ≤ j ^ 2) :
    reward (hardInstance k j ε τ) (valueOrdered m) =
        τ * m * k / j + ε * k * τ * m / j ^ 2 - m * k / j + expMinBinom m ((k : ℝ) / j) k ∧
    reward (hardInstance k j ε τ) (valueOrdered m) ≤
        ε * k * τ + k * m / j * (τ - 1) + expMinBinom m ((k : ℝ) / j) k := by sorry

end HiringLP.SimUpper
