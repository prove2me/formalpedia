-- Prove2me | Theorems.Thm_MinimalAccess_gamma_isStable
-- name    : MinimalAccess.gamma_isStable
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:44:05.722747+00:00
-- url     : https://prove2.me/theorems/ea1cb31c-fe53-4dfa-9cd1-172762d2eef3
-- title:
--   The deferred acceptance outcome $\gamma(P,\succ,r)$ is a stable matching
-- statement:
--   Throughout, $I$ is a finite set of students, $S$ a finite set of schools with capacities $q=(q_s)_{s\in S}$, $P=(P_i)_{i\in I}$ strict preferences over $S\cup\{\emptyset\}$ ($\emptyset$ the no-school option, $R_i$ the weak version of $P_i$), $\succ=(\succ_s)_{s\in S}$ strict priorities over $I$, and $r=(r(i))_{i\in I}$ minimal-access rights, $r(i)\subseteq S$.
--
--   For every problem $(P,\succ,r)$, the outcome $\gamma(P,\succ,r)$ of the student-proposing deferred acceptance algorithm based on adjusted priorities
--
--   1. is a matching (no school receives more than $q_s$ students);
--   2. is classically stable with respect to $(P,\succ^r)$;
--   3. is stable with respect to $(P,\succ,r)$.
--
--   The paper derives (2) from Gale–Shapley (1962) and (3) from (2) by Remark 1. It is the stability part of Lemma 1.
--
--   Differences from the source:
--   - encoding: finite sets I, S; no-school option ∅; strict preferences P_i over S ∪ {∅}; strict priorities ≻_s over I → I = Fin n, S = Fin m, ∅ = none; P i : Option (Fin m) ≃ Fin (m+1) and pri s : Fin n ≃ Fin n rank bijections, rank 0 most preferred / highest priority; reason: finite relabelling; every strict order is exactly one rank bijection, so the problems are the same
--   - encoding: γ(P, ≻, r): the student-proposing deferred acceptance algorithm on (P, ≻^r), Steps 0, 1, 2, … (pp.6–7) → gamma q P pri r = published GaleShapley1962.Admissions.Market.deferredAcceptance on the market with acceptable lists best first, all students ordered by adjKey pri r, quotas q; reason: the published procedure runs exactly these simultaneous rounds (fuel-bounded); same outcome
--   - encoding: 'the resulting matching' (capacities respected) → explicit conjunct IsMatching q (gamma q P pri r); reason: the source calls the output a matching; the clause makes that explicit
--   - generalization: capacities q_s ∈ N, positive (cf. q_s ≥ 1, p.29) → q : Fin m → ℕ, q_s = 0 allowed; reason: the statement for positive capacities is the special case; the argument never uses positivity
-- source:
--   Klaus–Klijn, Minimal-Access Rights in School Choice and the Deferred Acceptance Mechanism, BSE Working Paper 1264 (rev. July 2023), §2, p.7 (paragraph after the algorithm)

import Mathlib
import Definitions.Def_MinimalAccess_Model
import Definitions.Def_MinimalAccess_AdjustedPriorities
import Definitions.Def_MinimalAccess_DeferredAcceptance

namespace MinimalAccess

open GaleShapley1962.Admissions

/-- Klaus–Klijn, BSE Working Paper 1264 (rev. July 2023), p.7: "It follows from Gale and
Shapley (1962) (see also Abdulkadiroğlu and Sönmez, 2003, Proposition 1) that the resulting
matching is stable with respect to (P, ≻^r). Hence, by Remark 1, the (student-proposing) deferred
acceptance algorithm yields a matching that is stable with respect to (P, ≻, r)."

**Formalization Note.** `gamma q P pri r` is the published simultaneous applicant-proposing
deferred acceptance run on `(P, ≻^r)` (see `MinimalAccess.daKey`). The three clauses are: the
output is a matching (capacities respected, implicit in "matching"); it is classically stable
with respect to `(P, ≻^r)`; it is stable with respect to `(P, ≻, r)`. Any capacities
`q : Fin m → ℕ`, including `0`. -/
theorem gamma_isStable {n m : ℕ} (q : Fin m → ℕ) (P : Fin n → Pref m) (pri : Fin m → Prio n)
    (r : Fin n → Finset (Fin m)) :
    IsMatching q (gamma q P pri r) ∧
      IsClassicallyStable q P (adjKey pri r) (gamma q P pri r) ∧
      IsStable q P pri r (gamma q P pri r) := by sorry

end MinimalAccess
