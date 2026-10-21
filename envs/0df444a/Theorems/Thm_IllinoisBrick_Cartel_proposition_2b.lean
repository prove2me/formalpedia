-- Prove2me | Theorems.Thm_IllinoisBrick_Cartel_proposition_2b
-- name    : IllinoisBrick.Cartel.proposition_2b
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:42:57.221981+00:00
-- url     : https://prove2.me/theorems/ce0cd53c-7eb5-4d1c-bd72-a960984520aa
-- title:
--   Proposition 2 part b, p. 14 (PDF 15) — a cartel is possible under a WPFF contract
-- statement:
--   Assume $0 < b$ and $c < a$. There are admissible WPFF terms $v = [v_1, v_2]$ such that a retailer equilibrium under $v$ exists, and every retailer equilibrium $q$ under $v$ satisfies the cartel conditions against every retailer equilibrium $q^C$ under the competitive WPFF terms $v^C = \{w = c, f = 0\}$:
--   $$\Pi_j(v,q) > \Pi_j(v^C,q^C)\ \ (j = 1,2), \qquad \pi_i(v,q) \ge \pi_i(v^C,q^C)\ \ (i = 1,2).$$
--
--   The fixed fee lets the manufacturers raise the wholesale price, and with it the supply-chain profit, while returning enough to each retailer, as a slotting fee, that the retailers have no ground to sue.
--
--   **Formalization Note** "Can form a cartel" is read as: the terms admit a retailer equilibrium, and (C1) and (C2) hold at every one of them, so the claim cannot rest on a favourable choice among several equilibria.
-- source:
--   Jain, Hasija, Netessine, Supply chains and antitrust governance, accepted manuscript (Management Science 67(11), 2021; LBS Research Online eprint 1493), p. 14 (PDF 15), Proposition 2 part b

import Mathlib
import Definitions.Def_IllinoisBrick_Cartel_Model

namespace IllinoisBrick.Cartel

/-- Proposition 2 part b, p. 14: under the IB ruling the manufacturers can form a cartel under a
WPFF contract: there are admissible WPFF terms `v = [v₁, v₂]` under which a retailer equilibrium
exists, and every retailer equilibrium under `v` satisfies (C1) and (C2) against every retailer
equilibrium under the competitive terms. -/
theorem proposition_2b (a b c : ℝ) (h : Standing a b c) :
    ∃ v : Fin 2 → Terms, (∀ j, Admissible c Contract.WPFF (v j)) ∧
      (∃ q : Fin 2 → ℝ, IsRetailerEq a b c Contract.WPFF v q) ∧
      ∀ q qC : Fin 2 → ℝ, IsRetailerEq a b c Contract.WPFF v q →
        IsRetailerEq a b c Contract.WPFF (fun _ => competitiveTerms a b c Contract.WPFF) qC →
        IsCartel a b c Contract.WPFF v q qC := by sorry

end IllinoisBrick.Cartel
