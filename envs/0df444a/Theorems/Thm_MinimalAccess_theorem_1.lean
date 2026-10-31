-- Prove2me | Theorems.Thm_MinimalAccess_theorem_1
-- name    : MinimalAccess.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:44:03.889763+00:00
-- url     : https://prove2.me/theorems/43977e25-432a-44e3-825a-96cd3fb10cbf
-- title:
--   Theorem 1 (Characterization) — $\varphi$ is minimal-access stable, strategy-proof and minimal-access monotonic iff $\varphi=\gamma$
-- statement:
--   Throughout, $I$ is a finite set of students, $S$ a finite set of schools with capacities $q=(q_s)_{s\in S}$, $P=(P_i)_{i\in I}$ strict preferences over $S\cup\{\emptyset\}$ ($\emptyset$ the no-school option, $R_i$ the weak version of $P_i$), $\succ=(\succ_s)_{s\in S}$ strict priorities over $I$, and $r=(r(i))_{i\in I}$ minimal-access rights, $r(i)\subseteq S$.
--
--   Let $\gamma$ be the (minimal-access adjusted) deferred acceptance mechanism, i.e. student-proposing deferred acceptance run on the adjusted priorities $\succ^r$. A mechanism $\varphi$ is minimal-access stable, strategy-proof, and minimal-access monotonic if and only if
--
--   $$
--   \varphi=\gamma .
--   $$
--
--   So no mechanism satisfying these three properties can treat minimal-access rights differently from the adjusted-priority deferred acceptance mechanism.
--
--   Differences from the source:
--   - encoding: finite sets I, S; no-school option ∅; strict preferences P_i over S ∪ {∅}; strict priorities ≻_s over I → I = Fin n, S = Fin m, ∅ = none; P i : Option (Fin m) ≃ Fin (m+1) and pri s : Fin n ≃ Fin n rank bijections, rank 0 most preferred / highest priority; reason: finite relabelling; every strict order is exactly one rank bijection, so the problems are the same
--   - encoding: a mechanism selects a matching φ(P, ≻, r) for each problem → φ : Mechanism n m (a function of (P, pri, r) to assignments) with the hypothesis IsMechanism q φ (every output respects the capacities); reason: the same mechanisms; condition (iii) of a matching holds by the assignment encoding
--   - encoding: γ(P, ≻, r): the student-proposing deferred acceptance algorithm on (P, ≻^r), Steps 0, 1, 2, … (pp.6–7) → gamma q P pri r = published GaleShapley1962.Admissions.Market.deferredAcceptance on the market with acceptable lists best first, all students ordered by adjKey pri r, quotas q; reason: the published procedure runs exactly these simultaneous rounds (fuel-bounded); same outcome
--   - generalization: capacities q_s ∈ N, positive (cf. q_s ≥ 1, p.29) → q : Fin m → ℕ, q_s = 0 allowed; reason: the statement for positive capacities is the special case; the argument never uses positivity
-- source:
--   Klaus–Klijn, Minimal-Access Rights in School Choice and the Deferred Acceptance Mechanism, BSE Working Paper 1264 (rev. July 2023), Theorem 1 (Characterization), p.13

import Mathlib
import Definitions.Def_MinimalAccess_Model
import Definitions.Def_MinimalAccess_AdjustedPriorities
import Definitions.Def_MinimalAccess_DeferredAcceptance
import Definitions.Def_MinimalAccess_Mechanism

namespace MinimalAccess

open GaleShapley1962.Admissions

/-- Klaus–Klijn, *Minimal-Access Rights in School Choice and the Deferred Acceptance
Mechanism*, BSE Working Paper 1264 (rev. July 2023), Theorem 1 (Characterization), p.13: "A
mechanism φ is minimal-access stable, strategy-proof, and minimal-access monotonic if and only if
φ = γ."

**Formalization Note.** Students are `Fin n`, schools `Fin m` (any `n, m`), capacities any
`q : Fin m → ℕ` (including `0`); `none` is the no-school option ∅. Preferences and priorities are
rank bijections (rank `0` = most preferred / highest priority), so every input is a valid
problem and `φ = gamma q` is equality of functions on all problems `(P, ≻, r)`. `γ` is the
published simultaneous student-proposing deferred acceptance run on the adjusted priorities
`≻^r` (`MinimalAccess.gamma`). `IsMechanism q φ` says that `φ` selects a matching (capacities
respected) for each problem. Both directions of the equivalence are stated. -/
theorem theorem_1 {n m : ℕ} (q : Fin m → ℕ) (φ : Mechanism n m) (hφ : IsMechanism q φ) :
    (IsMinimalAccessStableMech q φ ∧ IsStrategyProof φ ∧ IsMinimalAccessMonotonic φ) ↔
      φ = gamma q := by sorry

end MinimalAccess
