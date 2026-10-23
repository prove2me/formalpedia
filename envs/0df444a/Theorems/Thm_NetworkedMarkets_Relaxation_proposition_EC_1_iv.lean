-- Prove2me | Theorems.Thm_NetworkedMarkets_Relaxation_proposition_EC_1_iv
-- name    : NetworkedMarkets.Relaxation.proposition_EC_1_iv
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-18T17:25:19.159754+00:00
-- url     : https://prove2.me/theorems/1d293b14-08a8-4198-8997-aa4d77f4ef1d
-- title:
--   Proposition EC.1(iv), p. ec3 (PDF 47), at problem (7) — all optimal solutions of (7) share the supply-demand vector
-- statement:
--   Under the standing assumptions and Assumptions 1–2, if $(x,q^s,q^b)$ and $(x',q'^s,q'^b)$ are both optimal solutions of the relaxation (7), then
--   $$q^s=q'^s\qquad\text{and}\qquad q^b=q'^b.$$
--
--   The optimal flow need not be unique, but the optimal supply-demand vector $(\bar q^s,\bar q^b)$ is; Theorem 1 is stated in terms of it.
--
--   **Formalization Note.** Instance of Proposition EC.1(iv) at Lemma EC.1(ii); the framework problem (EC.1) is not formalized.
-- source:
--   Birge, Candogan, Chen, Saban, Optimal Commissions and Subscriptions in Networked Markets, SSRN abstract 3259716 (version of 2019-09-13), p. ec3 (PDF 47), Proposition EC.1(iv), at the instance of Lemma EC.1(ii), p. ec4 (PDF 48); also p. 13

import Mathlib
import Definitions.Def_NetworkedMarkets_Relaxation_Setting

open Filter Topology

namespace NetworkedMarkets.Relaxation

theorem proposition_EC_1_iv {S B : Type*} [Fintype S] [Fintype B] [DecidableEq S] [DecidableEq B]
    (M : Market S B) (hM : M.Standing)
    (x : S → B → ℝ) (qs : S → ℝ) (qb : B → ℝ)
    (x' : S → B → ℝ) (qs' : S → ℝ) (qb' : B → ℝ)
    (hopt : M.IsOpt7 x qs qb) (hopt' : M.IsOpt7 x' qs' qb') :
    qs = qs' ∧ qb = qb' := by sorry

end NetworkedMarkets.Relaxation
