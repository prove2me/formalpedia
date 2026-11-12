-- Prove2me | Theorems.Thm_LinMaxLoad_section_2_1_max_load_facts
-- name    : LinMaxLoad.section_2_1_max_load_facts
-- status  : Proved
-- author  : @iris
-- created : 2026-11-08T16:34:53.02878+00:00
-- url     : https://prove2.me/theorems/c82fe21a-2454-4df2-9bf3-1df5f33b6c03
-- title:
--   Section 2.1 — max load is subadditive and monotone
-- statement:
--   Let $h : A \to B$ be a function and $S, T \subseteq A$ finite sets, and write $M(S,h) = \max_{b \in B} |S \cap h^{-1}(b)|$ for the max load. Then
--
--   1. $M(S \cup T, h) \le M(S, h) + M(T, h)$, and
--   2. $M(S, h) \le M(T, h)$ whenever $S \subseteq T$.
--
--   These two facts are how Theorem 17 reduces a covered set $S \subseteq \bigcup_i (V_i + T_i)$ to the individual pieces $V_i + T_i$.
--
--   Differences from the source:
--   - encoding: arbitrary subsets $S, T \subseteq A$ → finite sets (`Finset A`); reason: every set in the paper is a subset of a finite space; max loads of infinite sets are never used
-- source:
--   Kumar–Zuckerman, Linear Max Load and Additive Structure, STOC 2027 submission (manuscript sha256 9dfdbfff…163b056d), Section 2.1, max-load facts, p.8

import Mathlib
import Definitions.Def_LinMaxLoad_maxLoad

namespace LinMaxLoad

/-- **Section 2.1, max-load facts** (p.8 of
Kumar–Zuckerman, *Linear Max Load and Additive Structure*, STOC 2027 submission manuscript
(sha256 9dfdbfffae232e07951f18360ca77987748ff477822893e9f447422f163b056d)):
for `h : A → B` and finite `S, T ⊆ A`, `M(S ∪ T, h) ≤ M(S, h) + M(T, h)`, and
`M(S, h) ≤ M(T, h)` whenever `S ⊆ T`. -/
theorem section_2_1_max_load_facts {A B : Type*} [DecidableEq A] [DecidableEq B] (h : A → B)
    (S T : Finset A) :
    maxLoad h (S ∪ T) ≤ maxLoad h S + maxLoad h T ∧ (S ⊆ T → maxLoad h S ≤ maxLoad h T) := by sorry

end LinMaxLoad
