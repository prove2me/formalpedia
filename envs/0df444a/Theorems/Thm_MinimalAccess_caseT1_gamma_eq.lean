-- Prove2me | Theorems.Thm_MinimalAccess_caseT1_gamma_eq
-- name    : MinimalAccess.caseT1_gamma_eq
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:44:08.880407+00:00
-- url     : https://prove2.me/theorems/3ebbc7db-28ad-4149-b39a-713e69218bfb
-- title:
--   Case T1, reduction step — shrinking $r(i)$ to $\{s\}$ does not change $\gamma$ when $s$ is $i$'s only acceptable school
-- statement:
--   Throughout, $I$ is a finite set of students, $S$ a finite set of schools with capacities $q=(q_s)_{s\in S}$, $P=(P_i)_{i\in I}$ strict preferences over $S\cup\{\emptyset\}$ ($\emptyset$ the no-school option, $R_i$ the weak version of $P_i$), $\succ=(\succ_s)_{s\in S}$ strict priorities over $I$, and $r=(r(i))_{i\in I}$ minimal-access rights, $r(i)\subseteq S$.
--
--   Let $(P,\succ,r)$ be a problem, $i$ a student and $s$ a school such that $s$ is the only acceptable school for $i$ under $P_i$ and $s\in r(i)$. Let $r'$ be the rights with $r'(i)=\{s\}$ and $r'(\ell)=r(\ell)$ for $\ell\neq i$. Then
--
--   $$
--   \gamma(P,\succ,r')=\gamma(P,\succ,r).
--   $$
--
--   In particular $\gamma_i(P,\succ,r')=\gamma_i(P,\succ,r)$. This is the step that keeps $\varphi$ and $\gamma$ different while strictly reducing the total number of minimal-access rights.
--
--   Differences from the source:
--   - encoding: finite sets I, S; no-school option ∅; strict preferences P_i over S ∪ {∅}; strict priorities ≻_s over I → I = Fin n, S = Fin m, ∅ = none; P i : Option (Fin m) ≃ Fin (m+1) and pri s : Fin n ≃ Fin n rank bijections, rank 0 most preferred / highest priority; reason: finite relabelling; every strict order is exactly one rank bijection, so the problems are the same
--   - encoding: γ(P, ≻, r): the student-proposing deferred acceptance algorithm on (P, ≻^r), Steps 0, 1, 2, … (pp.6–7) → gamma q P pri r = published GaleShapley1962.Admissions.Market.deferredAcceptance on the market with acceptable lists best first, all students ordered by adjKey pri r, quotas q; reason: the published procedure runs exactly these simultaneous rounds (fuel-bounded); same outcome
--   - generalization: context of Case T1: i of Type 1 with justified max envy w.r.t. j and s at φ(P, ≻, r) (so s ∈ r(i) by (2)), µ*(i) = s the only acceptable school → only the hypotheses that s is the only acceptable school for i and s ∈ r(i); reason: the DA argument on the page uses only these two facts; the source's situation is a special case
--   - generalization: capacities q_s ∈ N, positive (cf. q_s ≥ 1, p.29) → q : Fin m → ℕ, q_s = 0 allowed; reason: the statement for positive capacities is the special case; the argument never uses positivity
-- source:
--   Klaus–Klijn, Minimal-Access Rights in School Choice and the Deferred Acceptance Mechanism, BSE Working Paper 1264 (rev. July 2023), Appendix A, Case T1, minimal-access rights reduction step, p.24

import Mathlib
import Definitions.Def_MinimalAccess_Model
import Definitions.Def_MinimalAccess_AdjustedPriorities
import Definitions.Def_MinimalAccess_DeferredAcceptance

namespace MinimalAccess

open GaleShapley1962.Admissions

/-- Klaus–Klijn, BSE Working Paper 1264 (rev. July 2023), Appendix A, Case T1, minimal-access
rights reduction step, p.24: with "r′(i) ≡ {s} and for each ℓ ∈ I∖{i}, r′(ℓ) ≡ r(ℓ)", "Recall that
µ*(i) = s is the only acceptable school under P_i and that under ≻^{r′}, student i retained his
minimal-access right at school µ*(i) = s while other students' minimal-access rights did not
change. Hence, for problems (P, ≻, r) and (P, ≻, r′), student i applies to school s at Step 1 of
the deferred acceptance algorithm. Since at school s, students' priorities did not change from
≻^r to ≻^{r′} and all students I∖{i} apply to the same schools in the consecutive steps of the
deferred acceptance algorithm, the resulting matchings for problems (P, ≻, r) and (P, ≻, r′) are
the same; particularly, ν*(i) = µ*(i) = s."

**Formalization Note.** The hypotheses are those of the page: `s` is the only acceptable school
for `i` under `P_i`, and `s ∈ r(i)` (in Case T1 `s` is the school of `i`'s envy, and
`s ∈ r(i)` by (2)). `r′ = Function.update r i {s}`. The conclusion is equality of the whole
matchings `γ(P, ≻, r′) = γ(P, ≻, r)`. Any capacities, including `0`. -/
theorem caseT1_gamma_eq {n m : ℕ} (q : Fin m → ℕ) (P : Fin n → Pref m) (pri : Fin m → Prio n)
    (r : Fin n → Finset (Fin m)) (i : Fin n) (s : Fin m)
    (honly : ∀ t, Acceptable P i t ↔ t = s) (hs : s ∈ r i) :
    gamma q P pri (Function.update r i {s}) = gamma q P pri r := by sorry

end MinimalAccess
