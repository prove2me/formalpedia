-- Prove2me | Theorems.Thm_MinimalAccess_eq_2
-- name    : MinimalAccess.eq_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:42:48.912987+00:00
-- url     : https://prove2.me/theorems/33ed9b17-73cb-4902-bddb-413e4c062a85
-- title:
--   Inequality (2) — max envy that is not min envy forces $|r(i)|>1$
-- statement:
--   Throughout, $I$ is a finite set of students, $S$ a finite set of schools with capacities $q=(q_s)_{s\in S}$, $P=(P_i)_{i\in I}$ strict preferences over $S\cup\{\emptyset\}$ ($\emptyset$ the no-school option, $R_i$ the weak version of $P_i$), $\succ=(\succ_s)_{s\in S}$ strict priorities over $I$, and $r=(r(i))_{i\in I}$ minimal-access rights, $r(i)\subseteq S$.
--
--   Let $\mu$ be any assignment (capacities not required), $i,j$ students and $s$ a school. Suppose $i$ has justified max envy at $\mu$ with respect to $j$ and $s$, but not justified min envy at $\mu$ with respect to $j$ and $s$. Then $\mu(j)=s\,P_i\,\mu(i)$, $s\in r(i)$, $s\notin r(j)$, $j\succ_s i$, there is a school $s'\in r(i)$ with $\mu(i)\,R_i\,s'$, and
--
--   $$
--   |r(i)|>1.
--   $$
--
--   In the uniqueness proof this guarantees that the student whose rights are reduced to a single school in Case T1 loses at least one right.
--
--   Differences from the source:
--   - encoding: finite sets I, S; no-school option ∅; strict preferences P_i over S ∪ {∅}; strict priorities ≻_s over I → I = Fin n, S = Fin m, ∅ = none; P i : Option (Fin m) ≃ Fin (m+1) and pri s : Fin n ≃ Fin n rank bijections, rank 0 most preferred / highest priority; reason: finite relabelling; every strict order is exactly one rank bijection, so the problems are the same
--   - generalization: (e.1) i has justified max envy at a minimal-access stable µ w.r.t. j ∈ I∖{i} and s; (e.2) no justified max envy at µ is justified min envy → for any assignment μ and any i, j, s: max envy of i w.r.t. (j, s) and no min envy of i w.r.t. the same (j, s); reason: (e.1) and (e.2) imply these pairwise hypotheses, and j ≠ i follows from them
-- source:
--   Klaus–Klijn, Minimal-Access Rights in School Choice and the Deferred Acceptance Mechanism, BSE Working Paper 1264 (rev. July 2023), Appendix A, inequality (2), p.24

import Mathlib
import Definitions.Def_MinimalAccess_Model
import Definitions.Def_MinimalAccess_AdjustedPriorities

namespace MinimalAccess

open GaleShapley1962.Admissions

/-- Klaus–Klijn, BSE Working Paper 1264 (rev. July 2023), Appendix A, inequality (2), p.24, from
"(e.1.) there exists some student i with justified max envy at µ with respect to some student
j ∈ I∖{i} and some school s ∈ S and (e.2.) any justified max envy at µ is not justified min envy.
Then, µ(j) = s P_i µ(i), s ∈ r(i), s ∉ r(j), j ≻_s i, and there is a school s′ ∈ S with s′ ∈ r(i)
and µ(i) R_i s′. Thus, |r(i)| > 1. (2)"

**Formalization Note.** Stated pairwise for an arbitrary assignment `μ`: if `i` has justified
max envy at `μ` with respect to `j` and `s`, and not justified min envy with respect to the same
`j` and `s`, then all the listed facts and `|r(i)| > 1` hold. `j ≻_s i` is
`pri s j < pri s i`; `µ(i) R_i s′` is `P i (μ i) ≤ P i (some s')`. -/
theorem eq_2 {n m : ℕ} (P : Fin n → Pref m) (pri : Fin m → Prio n) (r : Fin n → Finset (Fin m))
    (μ : Assignment n m) (i j : Fin n) (s : Fin m) (hmax : MaxEnvyAt P pri r μ i j s)
    (hmin : ¬ MinEnvyAt P pri r μ i j s) :
    μ j = some s ∧ P i (some s) < P i (μ i) ∧ s ∈ r i ∧ s ∉ r j ∧ pri s j < pri s i ∧
      (∃ s' ∈ r i, P i (μ i) ≤ P i (some s')) ∧ 1 < (r i).card := by sorry

end MinimalAccess
