-- Prove2me | Theorems.Thm_IllinoisBrick_Cartel_retailer_eq_linear
-- name    : IllinoisBrick.Cartel.retailer_eq_linear
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:42:53.228985+00:00
-- url     : https://prove2.me/theorems/ae3552d2-6e9d-4b99-b0cf-40567e56f5c3
-- title:
--   Problem (1), p. 8 (PDF 9), deterministic case — per-unit price w with fees f ≤ 0: unique retailer equilibrium q = (a − w)/(3b)
-- statement:
--   Assume $0 < b$. Suppose both manufacturers offer WPFF terms with the same wholesale price $w < a$ and fixed fees $f_1, f_2 \le 0$ (retailer $R_i$ pays $w q + f_i\,\mathbb I(q>0)$). Then a retailer equilibrium exists, and at every retailer equilibrium, for $i = 1, 2$,
--   $$q_i = \frac{a-w}{3b}, \qquad \pi_i = \frac{(a-w)^2}{9b} - f_i .$$
--
--   This is the closed-form solution of the retailers' problem (1) under deterministic demand and a per-unit price, with a slotting fee entering the retailers' profits only as a transfer. With $f_1 = f_2 = 0$ it is also the wholesale-price case.
--
--   **Formalization Note** The fees are restricted to $f_i \le 0$: a positive fee can make not buying optimal. The closed form is not printed in the paper; it is the solution of display (1).
-- source:
--   Jain, Hasija, Netessine, Supply chains and antitrust governance, accepted manuscript (Management Science 67(11), 2021; LBS Research Online eprint 1493), p. 8 (PDF 9), problem (1)

import Mathlib
import Definitions.Def_IllinoisBrick_Cartel_Model

namespace IllinoisBrick.Cartel

/-- Problem (1), p. 8, deterministic demand, per-unit price with a fixed fee: if both
manufacturers offer WPFF terms with the same wholesale price `w < a` and fixed fees `f₁, f₂ ≤ 0`,
a retailer equilibrium exists, and at every retailer equilibrium each retailer buys
`(a - w)/(3b)` and earns `(a - w)²/(9b) - f_i`. -/
theorem retailer_eq_linear (a b c w : ℝ) (hb : 0 < b) (hw : w < a) (v : Fin 2 → Terms)
    (hadm : ∀ i, Admissible c Contract.WPFF (v i)) (hvw : ∀ i, (v i).w = w)
    (hf : ∀ i, (v i).f ≤ 0) :
    (∃ q : Fin 2 → ℝ, IsRetailerEq a b c Contract.WPFF v q) ∧
    ∀ q : Fin 2 → ℝ, IsRetailerEq a b c Contract.WPFF v q →
      ∀ i : Fin 2, q i = (a - w) / (3 * b) ∧
        retailerProfit a b c Contract.WPFF v q i = (a - w) ^ 2 / (9 * b) - (v i).f := by sorry

end IllinoisBrick.Cartel
