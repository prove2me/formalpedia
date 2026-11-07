-- Prove2me | Theorems.Thm_KarpLiptonOM_theorem_A_3_3
-- name    : KarpLiptonOM.theorem_A_3_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:49:19.727141+00:00
-- url     : https://prove2.me/theorems/102292e5-f953-4073-bea4-477ce8aeb588
-- title:
--   Theorem A.3.3 — $\mathrm{OMIN} = \mathrm{OGTD}[\mathrm L^{\mathrm P}_2] = \mathrm P^{\mathrm{TALLY}\cap\mathrm L^{\mathrm P}_2}$
-- statement:
--   The following classes coincide:
--   $$
--   \mathrm{OMIN} = \mathrm{OGTD}[\mathrm L^{\mathrm P}_2] = \mathrm P^{\mathrm{TALLY} \cap \mathrm L^{\mathrm P}_2} .
--   $$
--   In particular, $\mathrm{OL}^{\mathrm P}_2 = \mathrm{OGTD}[\mathrm L^{\mathrm P}_2]$.
--
--   Here $\mathrm{OGTD}[\mathrm L^{\mathrm P}_2]$ is the class of languages with polynomial-size advice computable from $1^n$ by a polynomial-time machine with an oracle in $\mathrm L^{\mathrm P}_2$, and $\mathrm P^{\mathrm{TALLY} \cap \mathrm L^{\mathrm P}_2}$ the class of languages in $\mathrm P^T$ for a tally $T \in \mathrm L^{\mathrm P}_2$. This is part (1) of the paper's Theorem 4.
--
--   Differences from the source:
--   - encoding: deterministic polynomial-time oracle machines with loose access to a promise oracle → OracleTM (work and query tape, one step per query, time |w|^k + k with every oracle), correct with every language consistent with the oracle, repeated queries allowed; reason: the paper's own form of loose access for deterministic machines (p.21); a standard machine model, polynomially equivalent to the others; the paper's assumption that machines never repeat a query (p.21) changes no class when the oracle is a fixed language
--   - encoding: binary strings, lengths polynomial in n (polynomials nondecreasing and at least 1, p.20), polynomial-time predicates on tuples → List Bool, lengths p.eval n for p : Polynomial ℕ (p ≥ 1 imposed only in L₂^P, OL₂^P and OMIN), predicates on u₁#⋯#u_k decided by the published CookPvsNP Turing machines; reason: Lean convention; same classes (a length polynomial with p(0) = 0 gives no new language or promise problem)
--   - encoding: OGTD[L₂^P], P^{TALLY ∩ L₂^P} for the class L₂^P → OGTD over the promise problems (A, Ā), A ∈ L₂^P; the union of P^T over tally T ∈ L₂^P; reason: a class of languages as a class of promise problems (p.21); P^C as a union (Definition A.2.1)
-- source:
--   Hirsch–Volkovich, The Ultimate Karp–Lipton Collapse, STOC 2027 submission (manuscript sha256 aca09a2b…), Theorem A.3.3 (part (1) of Theorem 4), p.26

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_KarpLiptonOM_OMIN
import Definitions.Def_KarpLiptonOM_OLP2
import Definitions.Def_KarpLiptonOM_LP2
import Definitions.Def_KarpLiptonOM_OGTD
import Definitions.Def_KarpLiptonOM_InP
import Definitions.Def_KarpLiptonOM_IsTally
import Definitions.Def_KarpLiptonOM_toPromise

namespace KarpLiptonOM

/-- Theorem A.3.3 (part (1) of Theorem 4, p.26): `OMIN = OGTD[L₂^P] = P^{TALLY ∩ L₂^P}`; in particular `OL₂^P = OGTD[L₂^P]`.

Source: Hirsch–Volkovich, *The Ultimate Karp–Lipton Collapse*, STOC 2027 submission manuscript (sha256 aca09a2b…7c62fd1b).

**Formalization Note** Strings, machines and classes are those of the `KarpLiptonOM` definitions: oracle access through every language consistent with the oracle, lengths `Polynomial ℕ`, polynomial-time predicates decided by the published `CookPvsNP` machines. The item's natural-language statement lists every difference from the page. -/
theorem theorem_A_3_3 :
    OMIN = OGTD (toPromise '' LP2) Set.univ ∧
    OGTD (toPromise '' LP2) Set.univ =
      {L | ∃ T : Set (List Bool), IsTally T ∧ T ∈ LP2 ∧ InP (toPromise T) L} ∧
    OLP2 = OGTD (toPromise '' LP2) Set.univ := by sorry

end KarpLiptonOM
