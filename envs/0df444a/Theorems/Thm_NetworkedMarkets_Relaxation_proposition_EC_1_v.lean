-- Prove2me | Theorems.Thm_NetworkedMarkets_Relaxation_proposition_EC_1_v
-- name    : NetworkedMarkets.Relaxation.proposition_EC_1_v
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-18T17:25:28.121172+00:00
-- url     : https://prove2.me/theorems/88be76b1-921e-453d-8456-d7c5007d0324
-- title:
--   Proposition EC.1(v), p. ec4 (PDF 48), at problem (7) — at an optimum of (7) no buyer type trades its whole population
-- statement:
--   Under the standing assumptions and Assumptions 1–2, every optimal solution $(x,q^s,q^b)$ of the relaxation (7) satisfies
--   $$q^b_j<b_j\qquad\text{for all } j\in\mathcal B.$$
--
--   So the capacity constraint (7d) is never binding at an optimum, and its multiplier $\eta^b_j$ vanishes; this is used in Step (i-2) of the proof of Theorem 1.
--
--   **Formalization Note.** Instance of Proposition EC.1(v) at Lemma EC.1(ii), whose hypothesis (EC.1.1-3) holds there by Lemma EC.1(ii); the framework problem (EC.1) is not formalized.
-- source:
--   Birge, Candogan, Chen, Saban, Optimal Commissions and Subscriptions in Networked Markets, SSRN abstract 3259716 (version of 2019-09-13), p. ec4 (PDF 48), Proposition EC.1(v), at the instance of Lemma EC.1(ii)

import Mathlib
import Definitions.Def_NetworkedMarkets_Relaxation_Setting

open Filter Topology

namespace NetworkedMarkets.Relaxation

theorem proposition_EC_1_v {S B : Type*} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
    (M : Market S B) (hM : M.Standing)
    (x : S → B → ℝ) (qs : S → ℝ) (qb : B → ℝ) (hopt : M.IsOpt7 x qs qb) :
    ∀ j, qb j < M.b j := by sorry

end NetworkedMarkets.Relaxation
