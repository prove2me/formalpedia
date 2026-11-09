-- Prove2me | Theorems.Thm_MatchingGFT_TightE_proposition_2_1
-- name    : MatchingGFT.TightE.proposition_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:52:09.058488+00:00
-- url     : https://prove2.me/theorems/e1f1dbf6-3e7a-423c-a76f-cf00fb1ccb33
-- title:
--   Proposition 2.1 — GSOM and GBOM: one-sided optimality, DSIC, IR, WBB
-- statement:
--   For every market in the model and every tie-breaking order, $\Pi^S(\mathrm{GSOM})=\mathrm{OPT}^S$ and $\Pi^B(\mathrm{GBOM})=\mathrm{OPT}^B$, and each of GSOM and GBOM is DSIC, ex-post IR and ex-ante WBB. Point masses are allowed.
--
--   Differences from the source:
--   - encoding: a fixed strict order on the feasible family → an injective rank on the family, smaller rank preferred; reason: every strict order on a finite family arises this way
--   - encoding: a possibly randomized one-sided auction with realized payments → a lottery over the family with expected payments; reason: BIC, interim IR and the objective use expectations only
--   - encoding: interim and ex-ante expectations of payments → families are required to have integrable payments; reason: an expectation that is undefined has no meaning in the source; the requirement excludes only such families
--   - encoding: expected total payments (finite) → ex-ante WBB also states that both expected totals are integrable; reason: makes the Bochner integrals the source expectations
--   - reading: there are two-sided implementations of GSOM and GBOM → the statement is about the concrete mechanisms with normalized threshold payments; reason: PDF pp. 10–11 specify those payments as the mechanisms; this is the stronger reading
--   - encoding: Π = OPT as real numbers → equality in EReal of the real Π with the extended-real supremum; reason: OPT is a supremum whose finiteness is a proof obligation
-- source:
--   Xiaohui Bei, Wenhao Wu, Shengwei Zhou, STOC 2027 submission #465 (October 2026), Proposition 2.1, PDF p. 11

import Mathlib
import Definitions.Def_MatchingGFT_TightE_Market
import Definitions.Def_MatchingGFT_TightE_Mechanism
import Definitions.Def_MatchingGFT_TightE_OneSided

namespace MatchingGFT.TightE

/-- Proposition 2.1 (PDF p. 11): for every market in the model, including laws with point masses, the
concrete GSOM and GBOM satisfy `Π^S(GSOM) = OPT^S` and `Π^B(GBOM) = OPT^B`, and both are DSIC, ex-post IR
and ex-ante WBB. -/
theorem proposition_2_1 {B S : Type*} [Fintype B] [Fintype S] [DecidableEq B] [DecidableEq S]
    (m : Market B S) (hm : m.IsValid) (rank : Finset (B × S) → ℕ) (hrank : IsTieOrder m rank) :
    ((profitS m (gsom m rank) : ℝ) : EReal) = optS m ∧
    ((profitB m (gbom m rank) : ℝ) : EReal) = optB m ∧
    IsDSIC (fun _ => gsom m rank) ∧ IsExPostIR (fun _ => gsom m rank) ∧
      IsExAnteWBB m (fun _ => gsom m rank) ∧
    IsDSIC (fun _ => gbom m rank) ∧ IsExPostIR (fun _ => gbom m rank) ∧
      IsExAnteWBB m (fun _ => gbom m rank) := by sorry

end MatchingGFT.TightE
