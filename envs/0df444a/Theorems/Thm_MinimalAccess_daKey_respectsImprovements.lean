-- Prove2me | Theorems.Thm_MinimalAccess_daKey_respectsImprovements
-- name    : MinimalAccess.daKey_respectsImprovements
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:44:06.620774+00:00
-- url     : https://prove2.me/theorems/c1648384-ca6e-4e24-8197-a9502e281783
-- title:
--   Classical student-proposing deferred acceptance respects improvements (Balinski–Sönmez)
-- statement:
--   Let $I$, $S$, $q$ and $P$ be as in a classical school choice problem, and let $\succ$, $\succ'$ be strict priority profiles. Say that $\succ$ is an **improvement of $\succ'$ for student $i$** if
--
--   1. for every school $s$ and student $j$, $i\succ'_s j$ implies $i\succ_s j$; and
--   2. for every school $s$ and students $j,k\neq i$, $j\succ'_s k$ iff $j\succ_s k$.
--
--   Then student-proposing deferred acceptance makes $i$ weakly better off:
--
--   $$
--   \gamma_i(P,\succ)\;R_i\;\gamma_i(P,\succ').
--   $$
--
--   The paper cites Balinski–Sönmez (1999, Theorem 5) and applies it to $\succ^r$ versus $\succ^{r'}$ when only student $i$'s rights shrink from $r$ to $r'$, which shows that $\gamma$ is minimal-access monotonic.
--
--   Differences from the source:
--   - encoding: finite sets I, S; no-school option ∅; strict preferences P_i over S ∪ {∅}; strict priorities ≻_s over I → I = Fin n, S = Fin m, ∅ = none; P i : Option (Fin m) ≃ Fin (m+1) and pri s : Fin n ≃ Fin n rank bijections, rank 0 most preferred / highest priority; reason: finite relabelling; every strict order is exactly one rank bijection, so the problems are the same
--   - encoding: strict priority profiles ≻, ≻′ → injective key profiles key, key′; γ = daKey; reason: every strict order is given by injective keys and conversely
--   - reading: '≻^r is a so-called improvement of ≻^r′ for student i', stated through clause (1) only → hypotheses (1) h_up and (2) h_others (relative ranking of the other students unchanged); reason: clause (2) is part of the cited Balinski–Sönmez definition and holds for ≻^r vs ≻^r′ since only i's rights differ; without it the statement is false
--   - generalization: the cited fact used at ≻ = ≻^r, ≻′ = ≻^r′ → stated for every pair of injective key profiles satisfying (1), (2); reason: the cited theorem is the general classical statement; adjKey pri r vs adjKey pri r′ is a special case
--   - generalization: capacities q_s ∈ N, positive (cf. q_s ≥ 1, p.29) → q : Fin m → ℕ, q_s = 0 allowed; reason: the statement for positive capacities is the special case; the argument never uses positivity
-- source:
--   Klaus–Klijn, Minimal-Access Rights in School Choice and the Deferred Acceptance Mechanism, BSE Working Paper 1264 (rev. July 2023), proof of Lemma 1, p.12 (citing Balinski and Sönmez 1999, Theorem 5)

import Mathlib
import Definitions.Def_MinimalAccess_Model
import Definitions.Def_MinimalAccess_AdjustedPriorities
import Definitions.Def_MinimalAccess_DeferredAcceptance

namespace MinimalAccess

open GaleShapley1962.Admissions

/-- Klaus–Klijn, BSE Working Paper 1264 (rev. July 2023), proof of Lemma 1, p.12: "By Remark 1,
r and r′ induce adjusted priorities ≻^r and ≻^{r′} such that for each j ∈ I and each s ∈ S,
i ≻^{r′}_s j implies i ≻^r_s j. Hence, ≻^r is a so-called improvement of ≻^{r′} for student i and,
from Balinski and Sönmez (1999, Theorem 5), it follows that γ_i(P, ≻, r) = γ_i(P, ≻^r) R_i
γ_i(P, ≻^{r′}) = γ_i(P, ≻, r′)." The cited fact: classical student-proposing deferred acceptance
respects improvements.

**Formalization Note.** `key` is an improvement of `key'` for student `i` in the sense of
Balinski–Sönmez (1999): (a) whenever `i` is ranked above `j` at `s` under `key'`, she is
ranked above `j` under `key`; (b) the relative ranking of the other students `j, k ≠ i` is the
same under `key` and `key'`. Clause (b) is part of the cited definition and holds for
`adjKey pri r` vs `adjKey pri r'` because only `i`'s rights differ. Both key profiles are
injective. Any capacities, including `0`. -/
theorem daKey_respectsImprovements {n m : ℕ} (q : Fin m → ℕ) (P : Fin n → Pref m)
    (key key' : Fin m → Fin n → ℕ) (hkey : ∀ s, Function.Injective (key s))
    (hkey' : ∀ s, Function.Injective (key' s)) (i : Fin n)
    (h_up : ∀ s j, key' s i < key' s j → key s i < key s j)
    (h_others : ∀ s j k, j ≠ i → k ≠ i → (key' s j < key' s k ↔ key s j < key s k)) :
    P i (daKey q P key i) ≤ P i (daKey q P key' i) := by sorry

end MinimalAccess
