-- Prove2me | Theorems.Thm_MinimalAccess_start_not_stable
-- name    : MinimalAccess.start_not_stable
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:44:09.13553+00:00
-- url     : https://prove2.me/theorems/666cda40-1ae6-4645-b5f6-c9e7ad350aa7
-- title:
--   Appendix A, Start — under (t.a) and (t.b), $\varphi(P,\succ,r)$ is not stable
-- statement:
--   Throughout, $I$ is a finite set of students, $S$ a finite set of schools with capacities $q=(q_s)_{s\in S}$, $P=(P_i)_{i\in I}$ strict preferences over $S\cup\{\emptyset\}$ ($\emptyset$ the no-school option, $R_i$ the weak version of $P_i$), $\succ=(\succ_s)_{s\in S}$ strict priorities over $I$, and $r=(r(i))_{i\in I}$ minimal-access rights, $r(i)\subseteq S$.
--
--   Let $\mu^*=\gamma(P,\succ,r)$ and let $\mu$ be a matching (in the paper $\mu=\varphi(P,\succ,r)$) such that
--
--   1. (t.a) $\mu\neq\mu^*$, and
--   2. (t.b) every student $\ell$ with $\mu(\ell)\neq\mu^*(\ell)$ finds exactly one school acceptable.
--
--   Then $\mu$ is not stable with respect to $(P,\succ,r)$.
--
--   The paper argues via Remark 1 and the Rural Hospitals Theorem (the same students are matched at all stable matchings). Since $\varphi(P,\succ,r)$ is minimal-access stable, some student then has justified max envy that is not justified min envy.
--
--   Differences from the source:
--   - encoding: finite sets I, S; no-school option ∅; strict preferences P_i over S ∪ {∅}; strict priorities ≻_s over I → I = Fin n, S = Fin m, ∅ = none; P i : Option (Fin m) ≃ Fin (m+1) and pri s : Fin n ≃ Fin n rank bijections, rank 0 most preferred / highest priority; reason: finite relabelling; every strict order is exactly one rank bijection, so the problems are the same
--   - encoding: γ(P, ≻, r): the student-proposing deferred acceptance algorithm on (P, ≻^r), Steps 0, 1, 2, … (pp.6–7) → gamma q P pri r = published GaleShapley1962.Admissions.Market.deferredAcceptance on the market with acceptable lists best first, all students ordered by adjKey pri r, quotas q; reason: the published procedure runs exactly these simultaneous rounds (fuel-bounded); same outcome
--   - generalization: µ = φ(P, ≻, r) for φ satisfying the three axioms → any matching μ (capacities respected) satisfying (t.a) and (t.b) relative to γ(P, ≻, r); reason: φ(P, ≻, r) is such a matching; the argument uses only these properties
--   - generalization: capacities q_s ∈ N, positive (cf. q_s ≥ 1, p.29) → q : Fin m → ℕ, q_s = 0 allowed; reason: the statement for positive capacities is the special case; the argument never uses positivity
-- source:
--   Klaus–Klijn, Minimal-Access Rights in School Choice and the Deferred Acceptance Mechanism, BSE Working Paper 1264 (rev. July 2023), Appendix A, Start, p.24

import Mathlib
import Definitions.Def_MinimalAccess_Model
import Definitions.Def_MinimalAccess_AdjustedPriorities
import Definitions.Def_MinimalAccess_DeferredAcceptance
import Definitions.Def_MinimalAccess_StudentTypes

namespace MinimalAccess

open GaleShapley1962.Admissions

/-- Klaus–Klijn, BSE Working Paper 1264 (rev. July 2023), Appendix A, "Start", p.24, for a
problem satisfying (t.a) and (t.b) with µ ≡ φ(P, ≻, r) and µ* ≡ γ(P, ≻, r): "Suppose µ is stable
at (P, ≻, r). Then, since µ* is also stable at (P, ≻, r), it follows from Remark 1 and the Rural
Hospitals Theorem (see Footnote 6) that any student who is matched (to a school) at µ is also
matched (to a school) at µ*, and vice versa. Hence, all students are of Type 3. However, this
contradicts (t.a). So, µ is not stable at (P, ≻, r)."

**Formalization Note.** Stated for any matching `μ` (capacities respected) in the role of
`φ(P, ≻, r)`: if `μ` satisfies (t.a) `μ ≠ γ(P, ≻, r)` and (t.b) relative to `γ(P, ≻, r)`, then
`μ` is not stable at `(P, ≻, r)`. Any capacities, including `0`. -/
theorem start_not_stable {n m : ℕ} (q : Fin m → ℕ) (P : Fin n → Pref m) (pri : Fin m → Prio n)
    (r : Fin n → Finset (Fin m)) (μ : Assignment n m) (hμ : IsMatching q μ)
    (hta : μ ≠ gamma q P pri r) (htb : OneAcceptableWhereDiffer P μ (gamma q P pri r)) :
    ¬ IsStable q P pri r μ := by sorry

end MinimalAccess
