-- Prove2me | Theorems.Thm_IllinoisBrick_Cartel_proposition_1
-- name    : IllinoisBrick.Cartel.proposition_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:42:54.753001+00:00
-- url     : https://prove2.me/theorems/ed434ef8-4987-4fd2-b981-b7dc900737bf
-- title:
--   Proposition 1, p. 13 (PDF 14) — under the competitive terms every contract gives zero manufacturer profit and retailer profit (a − c)²/(9b)
-- statement:
--   Assume $0 < b$ and $c < a$, and fix one of the five contract structures. Suppose both manufacturers offer the competitive terms $v^C$ of Proposition 1 ($w = c$, all other terms $0$; under MOQ $q_{\min} = (a-c)/(4b)$). Then a retailer equilibrium exists, and at every retailer equilibrium $(q_1, q_2)$, for $i, j = 1, 2$,
--   $$q_i = \frac{a-c}{3b}, \qquad \Pi_j = 0, \qquad \pi_i = \frac{(a-c)^2}{9b}.$$
--
--   The manufacturers earn nothing and the retailers keep the whole supply-chain profit, under each contract alike. This is the competitive benchmark against which the cartel conditions (C1) and (C2) are measured.
--
--   **Formalization Note** Only the outcome at $v^C$ is stated; that $v^C$ solves the manufacturers' competitive problem (3) is not part of this item. The MOQ benchmark uses $q_{\min} = (a-c)/(4b)$, the reading disclosed in the model definition.
-- source:
--   Jain, Hasija, Netessine, Supply chains and antitrust governance, accepted manuscript (Management Science 67(11), 2021; LBS Research Online eprint 1493), p. 13 (PDF 14), Proposition 1

import Mathlib
import Definitions.Def_IllinoisBrick_Cartel_Model

namespace IllinoisBrick.Cartel

/-- Proposition 1 (outcome part), p. 13: under the competitive terms `v^C` offered by both
manufacturers, for every contract structure a retailer equilibrium exists, and at every retailer
equilibrium each retailer buys `(a - c)/(3b)`, each manufacturer earns `0` and each retailer earns
`(a - c)²/(9b)`. -/
theorem proposition_1 (a b c : ℝ) (h : Standing a b c) (k : Contract) :
    (∃ q : Fin 2 → ℝ, IsRetailerEq a b c k (fun _ => competitiveTerms a b c k) q) ∧
    ∀ q : Fin 2 → ℝ, IsRetailerEq a b c k (fun _ => competitiveTerms a b c k) q →
      ∀ i : Fin 2, q i = (a - c) / (3 * b) ∧
        manufacturerProfit a b c k (fun _ => competitiveTerms a b c k) q i = 0 ∧
        retailerProfit a b c k (fun _ => competitiveTerms a b c k) q i = (a - c) ^ 2 / (9 * b) := by sorry

end IllinoisBrick.Cartel
