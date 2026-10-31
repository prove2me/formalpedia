-- Prove2me | Theorems.Thm_LongShortSI_proposition_1_ii
-- name    : LongShortSI.proposition_1_ii
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:26:50.076281+00:00
-- url     : https://prove2.me/theorems/1b534ab5-2eb4-458a-bdfc-1c89d3339c68
-- title:
--   Proposition 1(ii) with Table 2 column SSNI — no inventory above $h^{SS}_I(d)$ (corrected: uniqueness only for $h>h^{SS}_I(d)$)
-- statement:
--   Let $a>0$ and $0\le d<1$. When both suppliers offer short-term contracts:
--
--   1. for every $h\ge h^{SS}_I(d)$ there is a subgame-perfect equilibrium in which each supplier sets the first-period price $w^{SSNI*}_1=\frac{a(1-d)}{2-d}$, no inventory is held, and the outcome is Table 2's SSNI column;
--   2. for every $h>h^{SS}_I(d)$, every subgame-perfect equilibrium has these first-period prices, holds no inventory, and has Table 2's SSNI outcome: $w^*_{i1}=w^*_{i2}=\frac{a(1-d)}{2-d}$, $q^*_{it}=s^*_{it}=\frac{a}{2(1+d)(2-d)}$, $\Pi^*_i=\frac{a^2(1-d)}{(2-d)^2(1+d)}$, $\pi^*=\frac{a^2}{(2-d)^2(1+d)}$.
--
--   Above the threshold strategic inventory disappears and the short-term contracts reproduce the long-term outcome, which is part (iii) of Proposition 3.
--
--   Differences from the source:
--   - reading: model conventions left implicit (pp.6–9) → "equilibrium" is a pure-strategy subgame-perfect equilibrium; wholesale prices range over [0, ∞); all quantities are ≥ 0; all stock is sold in period 2 (s_i2 = q_i2 + I_i) with no free disposal and no floor on market prices; production and selling costs are 0; the holding cost h is ≥ 0; reason: p.6 ("no units are salvaged", costs normalized to zero), ec2 ("at a non-negative wholesale price"), p.12 ("any non-negative holding cost") and ec6 ("for any 0 ≤ h < h^{SS}_I(d)"); the paper solves the game by backward induction
--   - reading: SS game: suppliers observe the reseller's inventory before period 2 (§3.1, p.8) → period-2 strategies are functions of the inventories (I_A, I_B) (and, for the reseller, of the period-2 prices); reason: the period-2 payoffs depend on nothing else; the paper's backward induction (ec1–ec4) uses exactly these histories
--   - correction: "for any h ≥ h^{SS}_I(d), there exists a unique equilibrium …" → existence for h ≥ h^{SS}_I(d); every SPE has these prices and no inventory for h > h^{SS}_I(d); reason: at h = h^{SS}_I(d) with d > 0 the SSI profile is also an equilibrium: the deviation gain is exactly zero (ec5) and I > 0 because h^{SS}_I(d) < h̄^{SS}(d); at d = 1/2: h^{SS}_I = 0.223967 < h̄^{SS} = 0.225572
--   - generalization: Proposition 1(ii) states the first-period price and no inventory; the outcome is reported in Table 2 → also asserts every row of Table 2's SSNI column; reason: Table 2 is the paper's statement of this equilibrium; the rows imply the printed claims
-- source:
--   Roy–Gilbert–Lai, The Implications of Strategic Inventory for Short-Term vs. Long-Term Supply Contracts in Nonexclusive Reselling Environments, SSRN 3752131 (version of 2022-04-20), Proposition 1(ii), p.11; Table 2 column SSNI, p.28; §EC.1.2, pp.ec5–ec6 (PDF 37–38)

import Mathlib
import Definitions.Def_LongShortSI_Model
import Definitions.Def_LongShortSI_ClosedForms

open scoped NNReal

namespace LongShortSI

/-- **Proposition 1(ii), p.11, with Table 2 column SSNI, p.28** (corrected: uniqueness only for
`h > h^{SS}_I(d)`). Roy–Gilbert–Lai, SSRN 3752131 (version of 2022-04-20).

For `a > 0`, `d ∈ [0, 1)`:
1. if `h ≥ h^{SS}_I(d)`, the SS game has a subgame-perfect equilibrium with first-period prices
   `a(1 − d)/(2 − d)`, no inventory, and Table 2's SSNI outcome;
2. if `h > h^{SS}_I(d)`, every subgame-perfect equilibrium of the SS game has these prices, no
   inventory, and Table 2's SSNI outcome.

**Formalization Note** At `h = h^{SS}_I(d)` with `d > 0` the SSI profile of Proposition 1(i) is
also an equilibrium (the deviation gain is exactly zero and `I > 0` since
`h^{SS}_I(d) < h̄^{SS}(d)`), so the printed "unique" holds for `h > h^{SS}_I(d)` only. -/
theorem proposition_1_ii (a d h : ℝ) (ha : 0 < a) (hd0 : 0 ≤ d) (hd1 : d < 1) :
    (hSSI a d ≤ h → ∃ σ : SSProfile, σ.IsSPE a d h ∧
      (σ.w1A : ℝ) = a * (1 - d) / (2 - d) ∧ (σ.w1B : ℝ) = a * (1 - d) / (2 - d) ∧
      MatchesSSNI a d (σ.outcome a d h)) ∧
    (hSSI a d < h → ∀ σ : SSProfile, σ.IsSPE a d h →
      (σ.w1A : ℝ) = a * (1 - d) / (2 - d) ∧ (σ.w1B : ℝ) = a * (1 - d) / (2 - d) ∧
      MatchesSSNI a d (σ.outcome a d h)) := by sorry

end LongShortSI
