-- Prove2me | Theorems.Thm_MinimalAccess_remark_1
-- name    : MinimalAccess.remark_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:42:47.421334+00:00
-- url     : https://prove2.me/theorems/072caa69-c7e7-4ae5-bd68-dff62c50c90d
-- title:
--   Remark 1 — justified max envy is justified envy under $\succ^r$; stability is classical stability for $(P,\succ^r)$
-- statement:
--   Throughout, $I$ is a finite set of students, $S$ a finite set of schools with capacities $q=(q_s)_{s\in S}$, $P=(P_i)_{i\in I}$ strict preferences over $S\cup\{\emptyset\}$ ($\emptyset$ the no-school option, $R_i$ the weak version of $P_i$), $\succ=(\succ_s)_{s\in S}$ strict priorities over $I$, and $r=(r(i))_{i\in I}$ minimal-access rights, $r(i)\subseteq S$.
--
--   Let $\succ^r$ be the adjusted priorities. For every matching $\mu$ and every student $i$:
--
--   1. $i$ has justified max envy at $\mu$ with respect to $(P,\succ,r)$ if and only if $i$ has justified envy at $\mu$ with respect to $(P,\succ^r)$;
--   2. $\mu$ is stable with respect to $(P,\succ,r)$ if and only if $\mu$ is classically stable with respect to $(P,\succ^r)$.
--
--   $$
--   \mu \text{ stable for } (P,\succ,r) \iff \mu \text{ classically stable for } (P,\succ^r).
--   $$
--
--   This reduces stability in the extended model to stability in a classical school choice problem, which is what lets the paper import the classical results on deferred acceptance.
--
--   Differences from the source:
--   - encoding: finite sets I, S; no-school option ∅; strict preferences P_i over S ∪ {∅}; strict priorities ≻_s over I → I = Fin n, S = Fin m, ∅ = none; P i : Option (Fin m) ≃ Fin (m+1) and pri s : Fin n ≃ Fin n rank bijections, rank 0 most preferred / highest priority; reason: finite relabelling; every strict order is exactly one rank bijection, so the problems are the same
--   - encoding: adjusted priorities ≻^r given by (1)–(3) of Remark 1 → keys adjKey pri r s i = (if s ∈ r i then 0 else n) + pri s i, i ≻^r_s j iff adjKey … i < adjKey … j; reason: the keys realise exactly (1)–(3): ranks are < n, so right-holders come first and ≻_s orders each group
--   - generalization: µ a matching → µ any assignment (capacities not required); reason: neither side of either equivalence uses the capacity bound; the statement for matchings is the special case
--   - generalization: capacities q_s ∈ N, positive (cf. q_s ≥ 1, p.29) → q : Fin m → ℕ, q_s = 0 allowed; reason: the statement for positive capacities is the special case; the argument never uses positivity
-- source:
--   Klaus–Klijn, Minimal-Access Rights in School Choice and the Deferred Acceptance Mechanism, BSE Working Paper 1264 (rev. July 2023), Remark 1, pp.5–6

import Mathlib
import Definitions.Def_MinimalAccess_Model
import Definitions.Def_MinimalAccess_AdjustedPriorities

namespace MinimalAccess

open GaleShapley1962.Admissions

/-- Klaus–Klijn, *Minimal-Access Rights in School Choice and the Deferred Acceptance
Mechanism*, BSE Working Paper 1264 (rev. July 2023), Remark 1 (Stability and adjusted
priorities), pp.5–6: "A student has justified max envy at a matching µ with respect to
(P, ≻, r) if and only if she has justified envy (Abdulkadiroğlu and Sönmez, 2003) at µ with
respect to (P, ≻^r) where ≻^r ≡ (≻^r_s)_{s∈S} are the adjusted priorities … Therefore, a matching
is stable with respect to (P, ≻, r) if and only if it is classically stable with respect to
(P, ≻^r)".

**Formalization Note.** Students `Fin n`, schools `Fin m`, `none` = ∅, rank `0` = most
preferred / highest priority. The adjusted priorities `≻^r` are the keys `adjKey pri r`
(right-holders at `s` first, `≻_s` inside each group), which realise (1)–(3) of Remark 1.
Both clauses of the remark are stated, the second for every assignment `μ` and every capacity
vector `q`. -/
theorem remark_1 {n m : ℕ} (q : Fin m → ℕ) (P : Fin n → Pref m) (pri : Fin m → Prio n)
    (r : Fin n → Finset (Fin m)) :
    (∀ (μ : Assignment n m) (i : Fin n),
      HasJustifiedMaxEnvy P pri r μ i ↔ HasClassicalEnvy P (adjKey pri r) μ i) ∧
    (∀ μ : Assignment n m, IsStable q P pri r μ ↔ IsClassicallyStable q P (adjKey pri r) μ) := by sorry

end MinimalAccess
