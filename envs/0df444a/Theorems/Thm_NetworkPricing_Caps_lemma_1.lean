-- Prove2me | Theorems.Thm_NetworkPricing_Caps_lemma_1
-- name    : NetworkPricing.Caps.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T07:16:32.404231+00:00
-- url     : https://prove2.me/theorems/ce74e8b0-3cd9-454e-b29a-a89109c1010e
-- title:
--   Lemma 1, p. 6 — raising tolls on E^< does not raise flow on some e₁ ∈ E^<, and gives a monotonicity inequality on some e₂ ∈ E^<
-- statement:
--   Consider an instance of the network pricing game satisfying the standing assumptions of §2.1 and having unique Wardrop link flows for all tolls $t \ge 0$, and let $x(t)$ be a selection of Wardrop flows (maximizers of the potential (1)).
--
--   Let $t, t' \ge 0$ be two toll vectors with $t \le t'$ such that $E^< = \{e \in E : t_e < t'_e\}$ is nonempty. Then there exist $e_1, e_2 \in E^<$ such that
--
--   1. $x_{e_1}(t') \le x_{e_1}(t)$;
--   2. $$\big[x_{e_2}(t') - x_{e_2}(t)\big]\,\big[\ell_{e_2}(x_{e_2}(t')) + t'_{e_2} - \ell_{e_2}(x_{e_2}(t)) - t_{e_2}\big] \le 0.$$
--
--   These two monotonicity properties of the Wardrop flow as a function of the tolls are the basic tools behind Lemma 2 and Theorem 1.
-- source:
--   Correa, Guzmán, Lianeas, Nikolova & Schröder, Network Pricing: How to Induce Optimal Flows Under Strategic Link Operators, Operations Research (Articles in Advance, 2021), doi:10.1287/opre.2020.2067, Lemma 1, p. 6

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Wardrop
import Definitions.Def_NetworkPricing_Caps_Model

namespace NetworkPricing.Caps

open KellyStochasticNetworks

theorem lemma_1 {J R Sd : ℕ} (I : Instance J R Sd) (hI : I.Standing) (hU : I.UniqueWardrop)
    (flow : (Fin J → ℝ) → Fin R → ℝ) (hflow : ∀ t : Fin J → ℝ, 0 ≤ t → I.IsWardropFlow t (flow t))
    (t t' : Fin J → ℝ) (ht : 0 ≤ t) (ht' : 0 ≤ t') (htt' : t ≤ t') (hne : ∃ e, t e < t' e) :
    (∃ e₁, t e₁ < t' e₁ ∧ linkFlow I.A (flow t') e₁ ≤ linkFlow I.A (flow t) e₁) ∧
    (∃ e₂, t e₂ < t' e₂ ∧
      (linkFlow I.A (flow t') e₂ - linkFlow I.A (flow t) e₂) *
        (I.ℓ e₂ (linkFlow I.A (flow t') e₂) + t' e₂
          - I.ℓ e₂ (linkFlow I.A (flow t) e₂) - t e₂) ≤ 0) := by sorry

end NetworkPricing.Caps
