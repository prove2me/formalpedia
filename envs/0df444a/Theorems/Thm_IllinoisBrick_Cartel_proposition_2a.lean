-- Prove2me | Theorems.Thm_IllinoisBrick_Cartel_proposition_2a
-- name    : IllinoisBrick.Cartel.proposition_2a
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:42:59.215439+00:00
-- url     : https://prove2.me/theorems/083c8379-a8c3-40cb-ad3f-1f1ccb966ca9
-- title:
--   Proposition 2 part a, p. 14 (PDF 15) — no cartel under WP, RS, QD or MOQ contracts
-- statement:
--   Assume $0 < b$ and $c < a$. Let the contract structure be WP, RS, QD or MOQ. Let $q^C$ be a retailer equilibrium when both manufacturers offer the competitive terms $v^C$, let $v = [v_1, v_2]$ be any admissible terms (equal or not), and let $q$ be a retailer equilibrium under $v$. Then the cartel conditions fail:
--   $$\neg\Big(\Pi_j(v,q) > \Pi_j(v^C,q^C)\ \forall j \ \text{ and }\ \pi_i(v,q) \ge \pi_i(v^C,q^C)\ \forall i\Big).$$
--
--   In the presence of the Illinois Brick ruling only the retailers, as direct purchasers, can sue the manufacturers, and they sue whenever collusion lowers their profit. Under these four contracts every collusive gain to the manufacturers costs the retailers, so no cartel survives.
--
--   **Formalization Note** The benchmark profits are the model's profits at $v^C$, not literals. Unequal terms are allowed, each retailer buying from its own manufacturer.
-- source:
--   Jain, Hasija, Netessine, Supply chains and antitrust governance, accepted manuscript (Management Science 67(11), 2021; LBS Research Online eprint 1493), p. 14 (PDF 15), Proposition 2 part a

import Mathlib
import Definitions.Def_IllinoisBrick_Cartel_Model

namespace IllinoisBrick.Cartel

/-- Proposition 2 part a, p. 14: under the IB ruling the manufacturers cannot form a cartel under a
WP, RS, QD or MOQ contract: for any admissible terms `v = [v₁, v₂]` (equal or not), any retailer
equilibrium `q` under `v` and any retailer equilibrium `qC` under the competitive terms,
conditions (C1) and (C2) do not both hold. -/
theorem proposition_2a (a b c : ℝ) (h : Standing a b c) (k : Contract) (hk : k ≠ Contract.WPFF)
    (qC : Fin 2 → ℝ) (hqC : IsRetailerEq a b c k (fun _ => competitiveTerms a b c k) qC)
    (v : Fin 2 → Terms) (hadm : ∀ j, Admissible c k (v j))
    (q : Fin 2 → ℝ) (hq : IsRetailerEq a b c k v q) :
    ¬ IsCartel a b c k v q qC := by sorry

end IllinoisBrick.Cartel
