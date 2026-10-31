-- Prove2me | Theorems.Thm_NetworkPricing_Caps_strong_nash_of_le_marginal
-- name    : NetworkPricing.Caps.strong_nash_of_le_marginal
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T07:16:41.000485+00:00
-- url     : https://prove2.me/theorems/73d9f3e8-259d-49f2-a42a-5c8e69569521
-- title:
--   Remark 1 and proof of Theorem 1, p. 7 — no capped coalition deviation from t̄ weakly improves all members and strictly one
-- statement:
--   Consider an instance of the network pricing game satisfying the standing assumptions of §2.1 and having unique Wardrop link flows for all tolls $t \ge 0$, let $x(t)$ be a selection of Wardrop flows, and write $\pi_e(t) = t_e\,x_e(t)$. Let $\bar t$ be an optimal toll vector, i.e. $\bar t \ge 0$ and $x(\bar t)$ has the link flows of an optimal flow $x^*$, and assume $\bar t \le \hat t$, where $\hat t_e = x^*_e\,\ell'_e(x^*_e)$ are the marginal tolls.
--
--   Then for every coalition $E^\Delta \subseteq E$ there is no $t'$ with $0 \le t' \le \bar t$ and $\{e : t'_e \neq \bar t_e\} \subseteq E^\Delta$ such that
--
--   $$
--   \pi_e(t') \ge \pi_e(\bar t) \ \text{ for all } e \in E^\Delta, \quad\text{with at least one strict inequality}.
--   $$
--
--   This is the property stronger than strong Nash equilibrium that Remark 1 says the proof of Theorem 1 establishes; it implies that $\bar t$ is a strong Nash equilibrium (hence a Nash equilibrium) of the game with caps $\bar t$.
--
--   **Formalization Note** No nonemptiness of $E^\Delta$ is needed: the required strict inequality forces $E^\Delta \neq \emptyset$.
-- source:
--   Correa, Guzmán, Lianeas, Nikolova & Schröder, Network Pricing: How to Induce Optimal Flows Under Strategic Link Operators, Operations Research (Articles in Advance, 2021), doi:10.1287/opre.2020.2067, Remark 1 and proof of Theorem 1, p. 7, "First, we prove that t̄ is a strong Nash equilibrium"

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Wardrop
import Definitions.Def_NetworkPricing_Caps_Model

namespace NetworkPricing.Caps

open KellyStochasticNetworks

theorem strong_nash_of_le_marginal {J R Sd : ℕ} (I : Instance J R Sd) (hI : I.Standing) (hU : I.UniqueWardrop)
    (flow : (Fin J → ℝ) → Fin R → ℝ) (hflow : ∀ t : Fin J → ℝ, 0 ≤ t → I.IsWardropFlow t (flow t))
    (tbar : Fin J → ℝ) (fstar : Fin R → ℝ) (hopt : I.IsOptimalToll flow fstar tbar)
    (hcap : ∀ e, tbar e ≤ I.marginalToll fstar e) :
    ∀ D : Finset (Fin J), ∀ t' : Fin J → ℝ, InCaps tbar t' → (∀ e ∉ D, t' e = tbar e) →
      ¬ ((∀ e ∈ D, I.profit flow tbar e ≤ I.profit flow t' e) ∧
          ∃ e ∈ D, I.profit flow tbar e < I.profit flow t' e) := by sorry

end NetworkPricing.Caps
