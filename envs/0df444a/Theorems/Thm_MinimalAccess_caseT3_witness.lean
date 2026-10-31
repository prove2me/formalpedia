-- Prove2me | Theorems.Thm_MinimalAccess_caseT3_witness
-- name    : MinimalAccess.caseT3_witness
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:44:26.431079+00:00
-- url     : https://prove2.me/theorems/57134bdb-c550-4668-8626-89d2931e3cc8
-- title:
--   Case T3 — a Type 3 envious student yields a Type 1 student with justified max envy
-- statement:
--   Throughout, $I$ is a finite set of students, $S$ a finite set of schools with capacities $q=(q_s)_{s\in S}$, $P=(P_i)_{i\in I}$ strict preferences over $S\cup\{\emptyset\}$ ($\emptyset$ the no-school option, $R_i$ the weak version of $P_i$), $\succ=(\succ_s)_{s\in S}$ strict priorities over $I$, and $r=(r(i))_{i\in I}$ minimal-access rights, $r(i)\subseteq S$.
--
--   Let $\mu^*=\gamma(P,\succ,r)$ and let $\mu$ be an individually rational matching (in the paper $\mu=\varphi(P,\succ,r)$) satisfying (t.b): every student $\ell$ with $\mu(\ell)\neq\mu^*(\ell)$ finds exactly one school acceptable. Let $i$ be a student of Type 3 who has justified max envy at $\mu$ with respect to student $j$ and school $s$. Then
--
--   1. $j$ is of Type 2; and
--   2. there is a student $k$ of Type 1 with $\mu^*(k)=s$ who has justified max envy at $\mu$ with respect to $j$ and $s$.
--
--   So, as in Case T1, some Type 1 student has justified max envy at $\mu$, and the rights-reduction step applies to her.
--
--   Differences from the source:
--   - encoding: finite sets I, S; no-school option ∅; strict preferences P_i over S ∪ {∅}; strict priorities ≻_s over I → I = Fin n, S = Fin m, ∅ = none; P i : Option (Fin m) ≃ Fin (m+1) and pri s : Fin n ≃ Fin n rank bijections, rank 0 most preferred / highest priority; reason: finite relabelling; every strict order is exactly one rank bijection, so the problems are the same
--   - encoding: γ(P, ≻, r): the student-proposing deferred acceptance algorithm on (P, ≻^r), Steps 0, 1, 2, … (pp.6–7) → gamma q P pri r = published GaleShapley1962.Admissions.Market.deferredAcceptance on the market with acceptable lists best first, all students ordered by adjKey pri r, quotas q; reason: the published procedure runs exactly these simultaneous rounds (fuel-bounded); same outcome
--   - generalization: µ = φ(P, ≻, r) for φ satisfying the three axioms at a problem satisfying (t.a), (t.b) → any matching μ that is individually rational and satisfies (t.b) relative to γ(P, ≻, r); reason: φ(P, ≻, r) is such a matching; the argument uses only these properties
--   - generalization: capacities q_s ∈ N, positive (cf. q_s ≥ 1, p.29) → q : Fin m → ℕ, q_s = 0 allowed; reason: the statement for positive capacities is the special case; the argument never uses positivity
-- source:
--   Klaus–Klijn, Minimal-Access Rights in School Choice and the Deferred Acceptance Mechanism, BSE Working Paper 1264 (rev. July 2023), Appendix A, Case T3, p.25

import Mathlib
import Definitions.Def_MinimalAccess_Model
import Definitions.Def_MinimalAccess_AdjustedPriorities
import Definitions.Def_MinimalAccess_DeferredAcceptance
import Definitions.Def_MinimalAccess_StudentTypes

namespace MinimalAccess

open GaleShapley1962.Admissions

/-- Klaus–Klijn, BSE Working Paper 1264 (rev. July 2023), Appendix A, Case T3, p.25, with
µ ≡ φ(P, ≻, r), µ* ≡ γ(P, ≻, r), a problem satisfying (t.b), and student i of Type 3 with
justified max envy at µ with respect to student j and school s: "So, by the Type Claim
(Claim 2), student j is of Type 2. Then, s = µ(j) is the only acceptable school for student j at
P_j and µ*(j) = ∅. Since γ is non-wasteful, there is a student k ∈ I such that µ*(k) = s and
µ(k) ≠ s. Obviously, student k is of Type 1. In particular, µ(k) = ∅. Since µ* is stable at
(P, ≻, r), it follows from µ*(k) = s P_j ∅ = µ*(j) and Remark 1 that k ≻^r_s j. Hence, at µ,
student k has justified max envy with respect to student j and school s."

**Formalization Note.** Stated for any matching `μ` in the role of `φ(P, ≻, r)` that respects
the capacities, is individually rational at `P` (as `φ(P, ≻, r)` is, by minimal-access
stability) and satisfies (t.b) relative to `γ(P, ≻, r)`. The conclusion has three clauses: `j`
is of Type 2; and some `k` is of Type 1, has `γ_k(P, ≻, r) = s`, and has justified max envy at
`μ` with respect to `j` and `s`. -/
theorem caseT3_witness {n m : ℕ} (q : Fin m → ℕ) (P : Fin n → Pref m) (pri : Fin m → Prio n)
    (r : Fin n → Finset (Fin m)) (μ : Assignment n m) (hμ : IsMatching q μ)
    (hIR : IsIndividuallyRational P μ) (htb : OneAcceptableWhereDiffer P μ (gamma q P pri r))
    (i j : Fin n) (s : Fin m) (hi : IsType3 P μ (gamma q P pri r) i)
    (henvy : MaxEnvyAt P pri r μ i j s) :
    IsType2 P μ (gamma q P pri r) j ∧
      ∃ k, IsType1 P μ (gamma q P pri r) k ∧ gamma q P pri r k = some s ∧
        MaxEnvyAt P pri r μ k j s := by sorry

end MinimalAccess
