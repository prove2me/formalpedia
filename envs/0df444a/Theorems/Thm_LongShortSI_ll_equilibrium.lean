-- Prove2me | Theorems.Thm_LongShortSI_ll_equilibrium
-- name    : LongShortSI.ll_equilibrium
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:26:52.561991+00:00
-- url     : https://prove2.me/theorems/85a8852c-5b3d-4c06-b1fb-7642176d36f9
-- title:
--   LL equilibrium (5)–(7): prices $w^{LL*}$, quantities $q^{LL*}$, no inventory (corrected: $w_{i2}$ and $I_i$ undetermined at $h=0$)
-- statement:
--   Both suppliers offer long-term contracts. Let $a>0$, $0\le d<1$, $h\ge0$, and
--   $$
--   w^{LL*}=a\,\frac{1-d}{2-d},\qquad q^{LL*}=\frac{a}{2(1+d)(2-d)},\qquad \pi^{LL*}=\frac{a^2}{(2-d)^2(1+d)},\qquad \Pi^{LL*}=\frac{a^2(1-d)}{(2-d)^2(1+d)}.
--   $$
--
--   1. The LL game has a subgame-perfect equilibrium in which $w_{it}=w^{LL*}$, $s_{it}=q_{it}=q^{LL*}$ for both suppliers and both periods, no inventory is held, $\Pi_i=\Pi^{LL*}$ and $\pi=\pi^{LL*}$.
--   2. In every subgame-perfect equilibrium, $w_{i1}=w^{LL*}$, $w_{i2}\ge w^{LL*}$, $s_{i1}=s_{i2}=q^{LL*}$, $\Pi_i=\Pi^{LL*}$ and $\pi=\pi^{LL*}$.
--   3. If $h>0$, every subgame-perfect equilibrium has exactly the outcome of 1.
--
--   The LL equilibrium is the benchmark against which Proposition 3 compares short-term contracts; it coincides with what would happen if the reseller could not hold inventory.
--
--   **Formalization Note** At $h=0$ the reseller can serve period 2 from period-1 stock at no cost, so a supplier who raises $w_{i2}$ above $w^{LL*}$ changes nothing: the second-period price and the split between $I_i$ and $q_{i2}$ are not determined there.
--
--   Differences from the source:
--   - reading: model conventions left implicit (pp.6–9) → "equilibrium" is a pure-strategy subgame-perfect equilibrium; wholesale prices range over [0, ∞); all quantities are ≥ 0; all stock is sold in period 2 (s_i2 = q_i2 + I_i) with no free disposal and no floor on market prices; production and selling costs are 0; the holding cost h is ≥ 0; reason: p.6 ("no units are salvaged", costs normalized to zero), ec2 ("at a non-negative wholesale price"), p.12 ("any non-negative holding cost") and ec6 ("for any 0 ≤ h < h^{SS}_I(d)"); the paper solves the game by backward induction
--   - reading: "we obtain the equilibrium …" (backward induction) → a subgame-perfect equilibrium with this outcome exists, and every subgame-perfect equilibrium has it; reason: existence guards against a vacuous equilibrium predicate (trap 16); uniqueness is what the paper's "the equilibrium" asserts
--   - correction: (5): w_it = w^{LL*} for t = 1, 2 and I_i = 0 in equilibrium, for every h ≥ 0 → every SPE has w_i1 = w^{LL*}, w_i2 ≥ w^{LL*}, sales q^{LL*} and profits (6)–(7); w_i2 = w^{LL*}, I_i = 0 and q_it = q^{LL*} for h > 0; reason: counterexample at h = 0 (allowed: "any non-negative holding cost", p.12): supplier A offering (w^{LL*}, 2w^{LL*}) with the reseller buying A's period-2 units in period 1 (I_A = q^{LL*}, q_A2 = 0) leaves every payoff and every incentive unchanged, so it is an SPE with w_A2 ≠ w^{LL*} and I_A > 0
-- source:
--   Roy–Gilbert–Lai, The Implications of Strategic Inventory for Short-Term vs. Long-Term Supply Contracts in Nonexclusive Reselling Environments, SSRN 3752131 (version of 2022-04-20), §4.1, (5)–(7), pp.9–10; Table 2 column LL, p.28

import Mathlib
import Definitions.Def_LongShortSI_Model
import Definitions.Def_LongShortSI_ClosedForms

open scoped NNReal

namespace LongShortSI

/-- **§4.1, (5)–(7), pp.9–10 — the LL equilibrium** (corrected at `h = 0`).
Roy–Gilbert–Lai, SSRN 3752131 (version of 2022-04-20).

For `a > 0`, `d ∈ [0, 1)`, `h ≥ 0`:
1. there is a subgame-perfect equilibrium of the LL game whose outcome is Table 2's LL column
   (prices `w^{LL*}`, purchases and sales `q^{LL*}`, no inventory, profits (6)–(7));
2. every subgame-perfect equilibrium has `w_i1 = w^{LL*}`, `w_i2 ≥ w^{LL*}`, sales
   `s_i1 = s_i2 = q^{LL*}`, `Π_i = Π^{LL*}` and `π = π^{LL*}`;
3. if `h > 0`, every subgame-perfect equilibrium has exactly Table 2's LL outcome.

**Formalization Note** At `h = 0` the second-period LL price is not determined: a supplier who
offers `(w^{LL*}, w_i2)` with `w_i2 > w^{LL*}` is served from inventory bought at `w^{LL*}` at no
holding cost, which leaves every payoff unchanged, so (5)'s `w_i2 = w^{LL*}` and `I_i = 0` hold
only for `h > 0` (correction). -/
theorem ll_equilibrium (a d h : ℝ) (ha : 0 < a) (hd0 : 0 ≤ d) (hd1 : d < 1) (hh : 0 ≤ h) :
    (∃ τ : LLProfile, τ.IsSPE a d h ∧ MatchesLL a d (τ.outcome a d h)) ∧
    (∀ τ : LLProfile, τ.IsSPE a d h →
      (∀ i, (τ.outcome a d h).w1 i = wLL a d ∧ wLL a d ≤ (τ.outcome a d h).w2 i ∧
        (τ.outcome a d h).s1 i = qLL a d ∧ (τ.outcome a d h).s2 i = qLL a d ∧
        (τ.outcome a d h).supplier i = PiLL a d) ∧
      (τ.outcome a d h).reseller = piLL a d ∧
      (0 < h → MatchesLL a d (τ.outcome a d h))) := by sorry

end LongShortSI
