-- Prove2me | Theorems.Thm_MinimalAccess_lemma_1
-- name    : MinimalAccess.lemma_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:43:59.981477+00:00
-- url     : https://prove2.me/theorems/01dc003d-2e74-4eac-954b-a43a6616d7d1
-- title:
--   Lemma 1 — $\gamma$ is stable, strategy-proof and minimal-access monotonic
-- statement:
--   Throughout, $I$ is a finite set of students, $S$ a finite set of schools with capacities $q=(q_s)_{s\in S}$, $P=(P_i)_{i\in I}$ strict preferences over $S\cup\{\emptyset\}$ ($\emptyset$ the no-school option, $R_i$ the weak version of $P_i$), $\succ=(\succ_s)_{s\in S}$ strict priorities over $I$, and $r=(r(i))_{i\in I}$ minimal-access rights, $r(i)\subseteq S$.
--
--   The (minimal-access adjusted) deferred acceptance mechanism $\gamma$
--
--   1. selects a matching for every problem;
--   2. is stable;
--   3. is strategy-proof;
--   4. is minimal-access monotonic.
--
--   Together with the fact that every stable matching is minimal-access stable, this is the "if" direction of Theorem 1.
--
--   Differences from the source:
--   - encoding: finite sets I, S; no-school option ∅; strict preferences P_i over S ∪ {∅}; strict priorities ≻_s over I → I = Fin n, S = Fin m, ∅ = none; P i : Option (Fin m) ≃ Fin (m+1) and pri s : Fin n ≃ Fin n rank bijections, rank 0 most preferred / highest priority; reason: finite relabelling; every strict order is exactly one rank bijection, so the problems are the same
--   - encoding: γ(P, ≻, r): the student-proposing deferred acceptance algorithm on (P, ≻^r), Steps 0, 1, 2, … (pp.6–7) → gamma q P pri r = published GaleShapley1962.Admissions.Market.deferredAcceptance on the market with acceptable lists best first, all students ordered by adjKey pri r, quotas q; reason: the published procedure runs exactly these simultaneous rounds (fuel-bounded); same outcome
--   - encoding: γ is a mechanism (selects a matching) → explicit conjunct IsMechanism q (gamma q); reason: the source calls γ a mechanism; the clause makes that explicit
--   - generalization: capacities q_s ∈ N, positive (cf. q_s ≥ 1, p.29) → q : Fin m → ℕ, q_s = 0 allowed; reason: the statement for positive capacities is the special case; the argument never uses positivity
-- source:
--   Klaus–Klijn, Minimal-Access Rights in School Choice and the Deferred Acceptance Mechanism, BSE Working Paper 1264 (rev. July 2023), Lemma 1, p.12

import Mathlib
import Definitions.Def_MinimalAccess_Model
import Definitions.Def_MinimalAccess_AdjustedPriorities
import Definitions.Def_MinimalAccess_DeferredAcceptance
import Definitions.Def_MinimalAccess_Mechanism

namespace MinimalAccess

open GaleShapley1962.Admissions

/-- Klaus–Klijn, BSE Working Paper 1264 (rev. July 2023), Lemma 1 (Properties of the deferred
acceptance mechanism), p.12: "The deferred acceptance mechanism γ is stable, strategy-proof, and
minimal-access monotonic."

**Formalization Note.** `gamma q` is the deferred acceptance mechanism based on adjusted
priorities for fixed students `Fin n`, schools `Fin m` and capacities `q` (any `q : Fin m → ℕ`,
including `0`). The first clause, `IsMechanism q (gamma q)` (every output respects the
capacities), is implicit in calling `γ` a mechanism; the other three are the lemma. -/
theorem lemma_1 {n m : ℕ} (q : Fin m → ℕ) :
    IsMechanism q (gamma q : Mechanism n m) ∧ IsStableMech q (gamma q : Mechanism n m) ∧
      IsStrategyProof (gamma q : Mechanism n m) ∧
      IsMinimalAccessMonotonic (gamma q : Mechanism n m) := by sorry

end MinimalAccess
