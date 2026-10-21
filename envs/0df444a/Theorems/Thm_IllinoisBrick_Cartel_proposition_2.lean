-- Prove2me | Theorems.Thm_IllinoisBrick_Cartel_proposition_2
-- name    : IllinoisBrick.Cartel.proposition_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:42:55.56647+00:00
-- url     : https://prove2.me/theorems/05bd14d4-f549-402c-a83f-3687c1c3bf72
-- title:
--   Proposition 2, p. 14 (PDF 15) — under the IB ruling no cartel forms under WP, RS, QD or MOQ contracts, one does under WPFF
-- statement:
--   Assume $0 < b$ and $c < a$ (deterministic demand $p = a - b(q_1+q_2)$, common marginal cost $c$). Then:
--
--   1. for each of the five contract structures, a retailer equilibrium $q^C$ under the competitive terms $[v^C, v^C]$ of Proposition 1 exists;
--   2. (part a) under a WP, RS, QD or MOQ contract the manufacturers cannot form a cartel: for every competitive retailer equilibrium $q^C$, all admissible terms $v = [v_1, v_2]$ and every retailer equilibrium $q$ under $v$,
--   $$\neg\big(\text{(C1)} \wedge \text{(C2)}\big), \quad \text{(C1)}: \Pi_j(v,q) > \Pi_j(v^C,q^C)\ \forall j, \quad \text{(C2)}: \pi_i(v,q) \ge \pi_i(v^C,q^C)\ \forall i;$$
--   3. (part b) under a WPFF contract they can: there are admissible WPFF terms $v$ with a retailer equilibrium, and (C1) and (C2) hold at every retailer equilibrium under $v$ against every competitive retailer equilibrium.
--
--   In the presence of the Illinois Brick ruling consumers cannot sue the manufacturers, and the retailers sue only if collusion lowers their profit. The theorem says that this leaves exactly one of the five contracts, the one with a fixed fee, under which the manufacturers can collude, and so explains slotting fees as a device for collusion.
--
--   **Formalization Note** The benchmark profits are computed in the model at $v^C$, not hard-coded. Part (a) allows unequal terms, each retailer buying from its own manufacturer. The standing assumptions, the MOQ benchmark $q_{\min} = (a-c)/(4b)$ and the admissible ranges are disclosed in the model definition.
-- source:
--   Jain, Hasija, Netessine, Supply chains and antitrust governance, accepted manuscript (Management Science 67(11), 2021; LBS Research Online eprint 1493), p. 14 (PDF 15), Proposition 2

import Mathlib
import Definitions.Def_IllinoisBrick_Cartel_Model

namespace IllinoisBrick.Cartel

/-- Proposition 2, p. 14 (deterministic demand). For every contract structure the competitive
benchmark (a retailer equilibrium under Proposition 1's terms `v^C`) exists, and in the presence
of the IB ruling the manufacturers
(a) cannot form a cartel under a WP, RS, QD or MOQ contract: for admissible terms `v`, a retailer
equilibrium `q` under `v` and a competitive retailer equilibrium `qC`, (C1) and (C2) fail
together;
(b) can form a cartel under a WPFF contract: some admissible WPFF terms have a retailer equilibrium,
and every retailer equilibrium under them satisfies (C1) and (C2) against every competitive one. -/
theorem proposition_2 (a b c : ℝ) (h : Standing a b c) :
    (∀ k : Contract,
      ∃ qC : Fin 2 → ℝ, IsRetailerEq a b c k (fun _ => competitiveTerms a b c k) qC) ∧
    (∀ k : Contract, k ≠ Contract.WPFF →
      ∀ qC : Fin 2 → ℝ, IsRetailerEq a b c k (fun _ => competitiveTerms a b c k) qC →
      ∀ v : Fin 2 → Terms, (∀ j, Admissible c k (v j)) →
      ∀ q : Fin 2 → ℝ, IsRetailerEq a b c k v q →
        ¬ IsCartel a b c k v q qC) ∧
    (∃ v : Fin 2 → Terms, (∀ j, Admissible c Contract.WPFF (v j)) ∧
      (∃ q : Fin 2 → ℝ, IsRetailerEq a b c Contract.WPFF v q) ∧
      ∀ q qC : Fin 2 → ℝ, IsRetailerEq a b c Contract.WPFF v q →
        IsRetailerEq a b c Contract.WPFF (fun _ => competitiveTerms a b c Contract.WPFF) qC →
        IsCartel a b c Contract.WPFF v q qC) := by sorry

end IllinoisBrick.Cartel
