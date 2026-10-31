-- Prove2me | Theorems.Thm_LongShortSI_proposition_3
-- name    : LongShortSI.proposition_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:26:54.690982+00:00
-- url     : https://prove2.me/theorems/f7945c1c-b535-4ec4-977e-b63cffa6042d
-- title:
--   Proposition 3 — suppliers prefer long-term contracts above $\widehat h(d)$ and for large $d$; the reseller prefers short-term ones for large $d$ (corrected: $\widehat h(0)=h^{SS}_I(0)$)
-- statement:
--   Let $a>0$, $0\le d<1$ and $h\ge0$. Compare the SSI equilibria of Proposition 1(i) (both suppliers offer short-term contracts and set the first-period price (8)) with the equilibria under long-term contracts (LL), by equilibrium profits. Let $h^{SS}_I(d)$ and $\widehat h(d)$ be the thresholds of Table 4. There are $d_1,d_2\in(0,1)$, not depending on $a$, such that:
--
--   1. $\widehat h(d)\le h^{SS}_I(d)$, strictly for $d>0$.
--   2. (i) For $h<\widehat h(d)$ each supplier earns strictly more under SS than under LL; for $\widehat h(d)<h<h^{SS}_I(d)$ each earns strictly more under LL. For $d>d_1$ each supplier earns strictly more under LL at every $h<h^{SS}_I(d)$, where inventory would be held under SS.
--   3. (ii) For $d>d_2$ the reseller earns strictly more under SS than under LL at every $h<h^{SS}_I(d)$: there is no longer any holding cost at which she prefers LL.
--   4. (iii) For $h>h^{SS}_I(d)$, every equilibrium under SS contracts holds no inventory, and its outcome (all prices, purchases, sales, inventories and profits) equals that of every equilibrium under LL contracts: the two are indistinguishable.
--   5. The equilibria compared exist: an SSI equilibrium for $h<h^{SS}_I(d)$, an LL equilibrium for every $h$, and an SS equilibrium for $h>h^{SS}_I(d)$.
--
--   In the exclusive case $d=0$ (Anand et al. 2008) a supplier always gains from the reseller's strategic inventory; with substitutable products the reseller's ability to stock a rival's product intensifies price competition, and for $d$ large enough the suppliers prefer long-term contracts while the reseller prefers short-term ones.
--
--   **Formalization Note** "For $d$ sufficiently large" is an existential threshold $d_0<1$, chosen before $a$ (the comparison is invariant under scaling $a$). The comparison in (i)–(ii) is made against every LL equilibrium; at $h=0$ these share their profits even though their inventories may differ.
--
--   Differences from the source:
--   - reading: model conventions left implicit (pp.6–9) → "equilibrium" is a pure-strategy subgame-perfect equilibrium; wholesale prices range over [0, ∞); all quantities are ≥ 0; all stock is sold in period 2 (s_i2 = q_i2 + I_i) with no free disposal and no floor on market prices; production and selling costs are 0; the holding cost h is ≥ 0; reason: p.6 ("no units are salvaged", costs normalized to zero), ec2 ("at a non-negative wholesale price"), p.12 ("any non-negative holding cost") and ec6 ("for any 0 ≤ h < h^{SS}_I(d)"); the paper solves the game by backward induction
--   - reading: SS game: suppliers observe the reseller's inventory before period 2 (§3.1, p.8) → period-2 strategies are functions of the inventories (I_A, I_B) (and, for the reseller, of the period-2 prices); reason: the period-2 payoffs depend on nothing else; the paper's backward induction (ec1–ec4) uses exactly these histories
--   - correction: "There exists a holding cost threshold ĥ(d) < h^{SS}_I(d)", for every d ∈ [0, 1) → ĥ(d) ≤ h^{SS}_I(d), strict for d > 0; reason: at d = 0 both equal a/4 (ec6: "ĥ(0) = h^{SS}_I(0)"; Table 4 gives a/4 for both), so the strict inequality fails; every other clause holds at d = 0
--   - generalization: "There exists a holding cost threshold ĥ(d)" → the explicit ĥ(d) = Q/((2 − d)²(1224 − …)) of Table 4; reason: Table 4 names this threshold; an explicit witness implies the existence claim
--   - generalization: "for d sufficiently large" (parts (i) and (ii)) → ∃ d₁, d₂ ∈ (0, 1) chosen before a, h; reason: a uniform threshold implies one chosen per a; profits scale with a², so the threshold is uniform
--   - generalization: Proposition 3 compares equilibria without asserting they exist → adds existence of an SSI equilibrium for h < h^{SS}_I(d), of an LL equilibrium, and of an SS equilibrium for h > h^{SS}_I(d); reason: without these the universally quantified comparisons could hold vacuously (trap 16); existence is Proposition 1 and §4.1
--   - reading: "the suppliers (reseller) strictly prefer SS contracts over LL contracts"; "SS" for h < h^{SS}_I(d) → strictly higher equilibrium profit, SS meaning an SPE with first-period prices (8) (Proposition 1(i)), LL meaning any SPE of the LL game; reason: p.11: "we focus on the SSI* and SSNI* equilibria, for h < h^{SS}_I(d) and h ≥ h^{SS}_I(d), respectively"; the proof (ec6) compares Π^{SSI*} and π^{SSI*} with the LL profits
--   - reading: (iii) "the SS and LL contracts are indistinguishable" → every SS equilibrium has no inventory and the same on-path outcome (prices, quantities, inventories, profits) as every LL equilibrium; reason: ec6: "the equilibrium is identical to that under LL contracts"; equality of every outcome entry is the strongest reading
-- source:
--   Roy–Gilbert–Lai, The Implications of Strategic Inventory for Short-Term vs. Long-Term Supply Contracts in Nonexclusive Reselling Environments, SSRN 3752131 (version of 2022-04-20), Proposition 3, p.12; Table 4 (ĥ, h^{SS}_I), p.29; proof §EC.3, p.ec6 (PDF 38)

import Mathlib
import Definitions.Def_LongShortSI_Model
import Definitions.Def_LongShortSI_ClosedForms

open scoped NNReal

namespace LongShortSI

/-- **Proposition 3, p.12 — suppliers' and reseller's preferences between SS and LL contracts**
(corrected: `ĥ(0) = h^{SS}_I(0)`). Roy–Gilbert–Lai, SSRN 3752131 (version of 2022-04-20).

There are `d₁, d₂ ∈ (0, 1)` such that for every `a > 0`, `d ∈ [0, 1)`, `h ≥ 0`, with "SS" the
SSI equilibria of Proposition 1(i) (first-period prices (8)) and "LL" any subgame-perfect
equilibrium of the LL game:
* `ĥ(d) ≤ h^{SS}_I(d)`, strictly for `d > 0` (Table 4's explicit `ĥ`);
* (i) for `h < ĥ(d)` each supplier earns strictly more under SS; for
  `ĥ(d) < h < h^{SS}_I(d)` strictly more under LL; for `d > d₁` strictly more under LL at every
  `h < h^{SS}_I(d)`;
* (ii) for `d > d₂` the reseller earns strictly more under SS at every `h < h^{SS}_I(d)`;
* (iii) for `h > h^{SS}_I(d)` every SS equilibrium holds no inventory and has the same outcome
  (prices, quantities, inventories and profits) as every LL equilibrium;
* the equilibria compared exist: SSI equilibria for `h < h^{SS}_I(d)`, LL equilibria always, SS
  equilibria for `h > h^{SS}_I(d)`.

**Formalization Note** "d sufficiently large" is `∃ d₀ < 1, ∀ d ∈ (d₀, 1)`, with `d₀` chosen before
`a`. The printed "`ĥ(d) < h^{SS}_I(d)`" fails at `d = 0`, where both equal `a/4`. -/
theorem proposition_3 :
    ∃ d1 d2 : ℝ, 0 < d1 ∧ d1 < 1 ∧ 0 < d2 ∧ d2 < 1 ∧
    ∀ a d h : ℝ, 0 < a → 0 ≤ d → d < 1 → 0 ≤ h →
      (hhat a d ≤ hSSI a d ∧ (0 < d → hhat a d < hSSI a d)) ∧
      (h < hhat a d → ∀ (σ : SSProfile) (τ : LLProfile),
        SSIEq a d h σ → τ.IsSPE a d h →
        ∀ i, (τ.outcome a d h).supplier i < (σ.outcome a d h).supplier i) ∧
      (hhat a d < h → h < hSSI a d → ∀ (σ : SSProfile) (τ : LLProfile),
        SSIEq a d h σ → τ.IsSPE a d h →
        ∀ i, (σ.outcome a d h).supplier i < (τ.outcome a d h).supplier i) ∧
      (d1 < d → h < hSSI a d → ∀ (σ : SSProfile) (τ : LLProfile),
        SSIEq a d h σ → τ.IsSPE a d h →
        ∀ i, (σ.outcome a d h).supplier i < (τ.outcome a d h).supplier i) ∧
      (d2 < d → h < hSSI a d → ∀ (σ : SSProfile) (τ : LLProfile),
        SSIEq a d h σ → τ.IsSPE a d h →
        (τ.outcome a d h).reseller < (σ.outcome a d h).reseller) ∧
      (hSSI a d < h → ∀ σ : SSProfile, σ.IsSPE a d h →
        (∀ i, (σ.outcome a d h).inv i = 0) ∧
        ∀ τ : LLProfile, τ.IsSPE a d h → σ.outcome a d h = τ.outcome a d h) ∧
      (h < hSSI a d → ∃ σ : SSProfile, SSIEq a d h σ) ∧
      (∃ τ : LLProfile, τ.IsSPE a d h) ∧
      (hSSI a d < h → ∃ σ : SSProfile, σ.IsSPE a d h) := by sorry

end LongShortSI
