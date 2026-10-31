-- Prove2me | Theorems.Thm_LongShortSI_proposition_1_i
-- name    : LongShortSI.proposition_1_i
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:26:49.39866+00:00
-- url     : https://prove2.me/theorems/cc55510d-94bd-4edd-9eec-d2d81f9bc71f
-- title:
--   Proposition 1(i) with Table 2 column SSI — the inventory equilibrium under short-term contracts (corrected: Table 2 row $s^*_{i1}$)
-- statement:
--   Let $a>0$, $0\le d<1$ and $0\le h<h^{SS}_I(d)$. When both suppliers offer short-term contracts there is a subgame-perfect equilibrium in which each supplier sets the first-period price
--   $$
--   w^{SSI*}_1=\frac{2a(3-d)^2(3+d)(1-d)-(2-d)(6-9d+d^3)h}{102-d(81-d(9+2(4-d)d))},\tag{8}
--   $$
--   and every subgame-perfect equilibrium with these first-period prices has the outcome of Table 2's SSI column: the second-period prices $w^*_{i2}$, purchases $q^*_{i1},q^*_{i2}$, sales $s^*_{i1},s^*_{i2}$ (with the sign of the $h$-term of $s^*_{i1}$ corrected), total purchases, inventories $I^*_i$, and profits $\Pi^*_i=Y/(2(1-d)(1+d)D^2)$, $\pi^*=X/(2(1-d)(1+d)D^2)$; in particular the reseller holds positive inventory of both products.
--
--   This is the equilibrium with strategic inventory whose profits Proposition 3 compares with long-term contracts.
--
--   Differences from the source:
--   - reading: model conventions left implicit (pp.6–9) → "equilibrium" is a pure-strategy subgame-perfect equilibrium; wholesale prices range over [0, ∞); all quantities are ≥ 0; all stock is sold in period 2 (s_i2 = q_i2 + I_i) with no free disposal and no floor on market prices; production and selling costs are 0; the holding cost h is ≥ 0; reason: p.6 ("no units are salvaged", costs normalized to zero), ec2 ("at a non-negative wholesale price"), p.12 ("any non-negative holding cost") and ec6 ("for any 0 ≤ h < h^{SS}_I(d)"); the paper solves the game by backward induction
--   - reading: SS game: suppliers observe the reseller's inventory before period 2 (§3.1, p.8) → period-2 strategies are functions of the inventories (I_A, I_B) (and, for the reseller, of the period-2 prices); reason: the period-2 payoffs depend on nothing else; the paper's backward induction (ec1–ec4) uses exactly these histories
--   - correction: Table 2 row s*_i1 and (EC.9): (3a(16 − d(3 + d)) − h(2 − d)(6 − 9d + d³))/(2(1 + d)D(d)) → + before the h-term; reason: at d = 1/2, h = 1/10, a = 1 the printed value is 0.219246, but (EC.6) at the price (8) and the table's own q*_i1 − I*_i both give 0.221760
--   - reading: "there exists an equilibrium in which each supplier sets his wholesale price to (8), and the reseller holds inventory of both products" → an SPE with first-period prices (8) exists, and every SPE with these prices has I_i > 0; reason: the "equilibrium in which" is the profile with prices (8); its on-path outcome is determined by those prices
--   - generalization: Proposition 1(i) states the price (8) and positive inventory; the outcome is reported in Table 2 → also asserts every row of Table 2's SSI column for every SPE with prices (8), except the supply-chain total π*_SC; reason: Table 2 is the paper's statement of this equilibrium; π*_SC = π* + 2Π* is a derived total whose printed Z (Table 5) does not equal π* + 2Π* and is not needed by any result
-- source:
--   Roy–Gilbert–Lai, The Implications of Strategic Inventory for Short-Term vs. Long-Term Supply Contracts in Nonexclusive Reselling Environments, SSRN 3752131 (version of 2022-04-20), Proposition 1(i), pp.10–11; (8), p.10; Table 2 column SSI, p.28; Table 5 (X, Y), p.29; (EC.8)–(EC.10), p.ec4 (PDF 36)

import Mathlib
import Definitions.Def_LongShortSI_Model
import Definitions.Def_LongShortSI_ClosedForms

open scoped NNReal

namespace LongShortSI

/-- **Proposition 1(i), pp.10–11, with Table 2 column SSI, p.28** (corrected: Table 2 row `s*_i1`).
Roy–Gilbert–Lai, SSRN 3752131 (version of 2022-04-20).

For `a > 0`, `d ∈ [0, 1)` and `0 ≤ h < h^{SS}_I(d)`, the SS game has a subgame-perfect
equilibrium in which both suppliers set the first-period price (8); and every such equilibrium has
Table 2's SSI outcome (every row, with the sign of the `h`-term of `s*_i1` corrected) and positive
inventory of both products. -/
theorem proposition_1_i (a d h : ℝ) (ha : 0 < a) (hd0 : 0 ≤ d) (hd1 : d < 1) (hh0 : 0 ≤ h)
    (hh : h < hSSI a d) :
    (∃ σ : SSProfile, SSIEq a d h σ) ∧
    ∀ σ : SSProfile, SSIEq a d h σ →
      MatchesSSI a d h (σ.outcome a d h) ∧ ∀ i, 0 < (σ.outcome a d h).inv i := by sorry

end LongShortSI
