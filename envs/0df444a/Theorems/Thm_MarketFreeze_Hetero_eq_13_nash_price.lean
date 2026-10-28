-- Prove2me | Theorems.Thm_MarketFreeze_Hetero_eq_13_nash_price
-- name    : MarketFreeze.Hetero.eq_13_nash_price
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-21T00:32:44.899921+00:00
-- url     : https://prove2.me/theorems/92915f39-c1b9-4602-993e-197a0fa5a4dd
-- title:
--   (12)–(13), p. 17 — the Nash bargaining price p = X − (X − I)/(1 + n) is the unique maximizer on [I, X] and increases in n
-- statement:
--   Suppose a good loan pays $X>I$ and the buyer/seller ratio is $n\ge0$. Let the buyer's bargaining weight be $\beta=1/(1+n)$. Among feasible prices $p\in[I,X]$, the Nash product $(X-p)^\beta(p-I)^{1-\beta}$ has the unique maximizer
--
--   $$p=X-\frac{X-I}{1+n}.$$
--
--   The maximizing price lies in $[I,X]$ and increases strictly with market tightness. This determines the transaction price used throughout the trading equilibrium.
--
--   **Formalization Note** The maximization is over the feasible bargaining interval $[I,X]$, where both gains are nonnegative; the endpoint $n=0$ is included.
-- source:
--   Song & Thakor, Market Freeze and Bank Capital Structure Heterogeneity, SSRN 3667175 (version of 2022-02-21; forthcoming Management Science, doi:10.1287/mnsc.2022.4374), equations (12)–(13), p. 17

import Mathlib
import Definitions.Def_MarketFreeze_Hetero_Model

namespace MarketFreeze.Hetero

theorem eq_13_nash_price (P : Params) (hXI : P.I < P.X)
    (n : ℝ) (hn : 0 ≤ n) :
    price P n ∈ Set.Icc P.I P.X ∧
    (∀ p ∈ Set.Icc P.I P.X, nashProduct P n p ≤ nashProduct P n (price P n)) ∧
    (∀ p ∈ Set.Icc P.I P.X,
      nashProduct P n p = nashProduct P n (price P n) → p = price P n) ∧
    StrictMonoOn (price P) (Set.Ici 0) := by sorry

end MarketFreeze.Hetero
