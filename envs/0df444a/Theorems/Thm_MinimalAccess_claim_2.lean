-- Prove2me | Theorems.Thm_MinimalAccess_claim_2
-- name    : MinimalAccess.claim_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:44:33.515448+00:00
-- url     : https://prove2.me/theorems/fc36cd80-66b4-4189-a9fd-93bfccc6276d
-- title:
--   Claim 2 (Type Claim) — every student is of exactly one of Types 1, 2, 3
-- statement:
--   Throughout, $I$ is a finite set of students, $S$ a finite set of schools with capacities $q=(q_s)_{s\in S}$, $P=(P_i)_{i\in I}$ strict preferences over $S\cup\{\emptyset\}$ ($\emptyset$ the no-school option, $R_i$ the weak version of $P_i$), $\succ=(\succ_s)_{s\in S}$ strict priorities over $I$, and $r=(r(i))_{i\in I}$ minimal-access rights, $r(i)\subseteq S$.
--
--   Let $\mu$ be an individually rational assignment, capacities not required (in the paper $\mu=\varphi(P,\succ,r)$) and $\mu^*=\gamma(P,\succ,r)$, and assume (t.b): every student $\ell$ with $\mu(\ell)\neq\mu^*(\ell)$ finds exactly one school acceptable. Then each student $\ell$ is of exactly one of the following types:
--
--   1. Type 1: $\mu^*(\ell)\in S$ is the only acceptable school under $P_\ell$ and $\mu(\ell)=\emptyset$;
--   2. Type 2: $\mu(\ell)\in S$ is the only acceptable school under $P_\ell$ and $\mu^*(\ell)=\emptyset$;
--   3. Type 3: $\mu(\ell)=\mu^*(\ell)\,R_\ell\,\emptyset$.
--
--   The partition into types drives the case analysis in the uniqueness proof of Theorem 1.
--
--   Differences from the source:
--   - encoding: finite sets I, S; no-school option ∅; strict preferences P_i over S ∪ {∅}; strict priorities ≻_s over I → I = Fin n, S = Fin m, ∅ = none; P i : Option (Fin m) ≃ Fin (m+1) and pri s : Fin n ≃ Fin n rank bijections, rank 0 most preferred / highest priority; reason: finite relabelling; every strict order is exactly one rank bijection, so the problems are the same
--   - encoding: γ(P, ≻, r): the student-proposing deferred acceptance algorithm on (P, ≻^r), Steps 0, 1, 2, … (pp.6–7) → gamma q P pri r = published GaleShapley1962.Admissions.Market.deferredAcceptance on the market with acceptable lists best first, all students ordered by adjKey pri r, quotas q; reason: the published procedure runs exactly these simultaneous rounds (fuel-bounded); same outcome
--   - generalization: φ(P, ≻, r) for φ minimal-access stable, strategy-proof, minimal-access monotonic, at a problem satisfying (t.a), (t.b) → any individually rational assignment μ satisfying (t.b) relative to γ(P, ≻, r); reason: φ(P, ≻, r) is such an assignment; the claim uses only individual rationality and (t.b)
--   - encoding: 'exactly of one of the following types' → disjunction of the three types and their three pairwise exclusions; reason: the same assertion
--   - generalization: capacities q_s ∈ N, positive (cf. q_s ≥ 1, p.29) → q : Fin m → ℕ, q_s = 0 allowed; reason: the statement for positive capacities is the special case; the argument never uses positivity
-- source:
--   Klaus–Klijn, Minimal-Access Rights in School Choice and the Deferred Acceptance Mechanism, BSE Working Paper 1264 (rev. July 2023), Appendix A, Claim 2 (Type Claim), p.23

import Mathlib
import Definitions.Def_MinimalAccess_Model
import Definitions.Def_MinimalAccess_AdjustedPriorities
import Definitions.Def_MinimalAccess_DeferredAcceptance
import Definitions.Def_MinimalAccess_StudentTypes

namespace MinimalAccess

open GaleShapley1962.Admissions

/-- Klaus–Klijn, BSE Working Paper 1264 (rev. July 2023), Appendix A, Claim 2 (Type Claim),
p.23, for a problem satisfying (t.b) (display (1), p.23) and with φ individually rational: "Each
student ℓ is exactly of one of the following types: Type 1: γ_ℓ(P, ≻, r) ∈ S is the only
acceptable school under P_ℓ and φ_ℓ(P, ≻, r) = ∅. Type 2: φ_ℓ(P, ≻, r) ∈ S is the only acceptable
school under P_ℓ and γ_ℓ(P, ≻, r) = ∅. Type 3: φ_ℓ(P, ≻, r) = γ_ℓ(P, ≻, r) R_ℓ ∅."

**Formalization Note.** The claim is stated for any assignment `μ` in the role of
`φ(P, ≻, r)` that is individually rational at `P` and satisfies (t.b) relative to
`μ* = γ(P, ≻, r)`; the paper's `φ(P, ≻, r)` is such a `μ`. "Exactly one" is the disjunction of
the three types together with their pairwise exclusion. -/
theorem claim_2 {n m : ℕ} (q : Fin m → ℕ) (P : Fin n → Pref m) (pri : Fin m → Prio n)
    (r : Fin n → Finset (Fin m)) (μ : Assignment n m) (hIR : IsIndividuallyRational P μ)
    (htb : OneAcceptableWhereDiffer P μ (gamma q P pri r)) (ℓ : Fin n) :
    (IsType1 P μ (gamma q P pri r) ℓ ∨ IsType2 P μ (gamma q P pri r) ℓ ∨
        IsType3 P μ (gamma q P pri r) ℓ) ∧
      ¬ (IsType1 P μ (gamma q P pri r) ℓ ∧ IsType2 P μ (gamma q P pri r) ℓ) ∧
      ¬ (IsType1 P μ (gamma q P pri r) ℓ ∧ IsType3 P μ (gamma q P pri r) ℓ) ∧
      ¬ (IsType2 P μ (gamma q P pri r) ℓ ∧ IsType3 P μ (gamma q P pri r) ℓ) := by sorry

end MinimalAccess
