-- Prove2me | Theorems.Thm_GaleShapley1962_Admissions_theorem_2
-- name    : GaleShapley1962.Admissions.theorem_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-30T02:41:52.562626+00:00
-- url     : https://prove2.me/theorems/bda221a2-ff1e-499e-aff7-3a6e16617741
-- title:
--   Theorem 2 — Applicant optimality of deferred acceptance
-- statement:
--   Let $M$ be any finite admissions market with arbitrary college quotas and strict, possibly incomplete acceptable lists on both sides. Let $\mu^*$ be the assignment computed by the simultaneous applicant-proposing deferred-acceptance procedure from empty waiting lists. Using exactly the printed Section 2 stability definition, the Section 5 preamble and Theorem 2 assert
--
--   $$\operatorname{Feasible}(\mu^*)\;\land\;\operatorname{PrintedStable}(\mu^*)\;\land\;\forall\mu,\ \operatorname{Feasible}(\mu)\land\operatorname{PrintedStable}(\mu)\Longrightarrow\forall a,\ \mu^*(a)\succeq_a\mu(a).$$
--
--   Every applicant is compared, including applicants left unassigned; every acceptable placement is preferred to unassignment. Comparison assignments obey acceptability and quotas but need not fill vacancies. Printed instability requires two applicants assigned to actual colleges, with the second preferring the first college and that college preferring the second applicant. No unmatched-applicant or vacant-seat block is added. The statement retains the printed claim; the counterexample under this literal convention is recorded separately in I1.
--
--   Differences from the source:
--   - encoding: n applicants and m colleges with strictly ordered acceptable lists → Fin n and Fin m with duplicate-free best-first lists; reason: finite relabeling and explicit strictness change no positive-population instance.
--   - encoding: applicants may remain unassigned and acceptable placements are preferred → Option (Fin m), with none for unassignment and guarded list-index comparisons; reason: represents the outside outcome without a fictitious college or a default rank for an omitted partner.
--   - encoding: iterate simultaneous waiting-list rounds until no applicant can apply → recursion for the number of permissible pairs, with stationary padding; reason: each productive round consumes a new pair, so this computes the same terminal assignment.
--   - generalization: the admissions discussion presumes populations of applicants and colleges and positive available quotas → also allow empty populations and zero quotas; reason: these boundary cases have empty waiting lists or retain nobody, and positive populations and quotas recover every source instance.
-- source:
--   Gale and Shapley (1962), College Admissions and the Stability of Marriage, Section 5 preamble and Theorem 2, printed p. 14 (PDF p. 6), with Section 2 displayed stability definition, printed p. 10 (PDF p. 2), https://doi.org/10.1080/00029890.1962.11989827

import Definitions.Def_GaleShapley1962_Admissions_Procedure

namespace GaleShapley1962.Admissions

theorem theorem_2 {n m : ℕ} (M : Market n m) :
    M.Feasible M.deferredAcceptance ∧
    M.PrintedStable M.deferredAcceptance ∧
    ∀ μ : Assignment n m, M.Feasible μ → M.PrintedStable μ →
      ∀ a : Fin n, M.WeaklyPrefers a (M.deferredAcceptance a) (μ a) := by sorry

end GaleShapley1962.Admissions
