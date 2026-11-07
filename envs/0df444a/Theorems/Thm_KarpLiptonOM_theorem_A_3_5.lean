-- Prove2me | Theorems.Thm_KarpLiptonOM_theorem_A_3_5
-- name    : KarpLiptonOM.theorem_A_3_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:49:10.096128+00:00
-- url     : https://prove2.me/theorems/7231224e-e0ac-4ce3-b76f-3c0f695f5a86
-- title:
--   Theorem A.3.5 — $\mathrm{OGTD}[\mathrm{prMA}] \subseteq \mathrm{OL}^{\mathrm P}_2$
-- statement:
--   Languages with polynomial-size advice computable from $1^n$ in polynomial time with a prMA oracle are in $\mathrm{OL}^{\mathrm P}_2$:
--   $$
--   \mathrm{OGTD}[\mathrm{prMA}] \subseteq \mathrm{OL}^{\mathrm P}_2 .
--   $$
--
--   Replacing the Merlin–Arthur oracle by a fixed language in $\mathrm L^{\mathrm P}_2$ makes the advice canonical, so the tally argument of Theorem A.3.3 applies. This is part (2) of the paper's Theorem 4.
--
--   Differences from the source:
--   - encoding: deterministic polynomial-time oracle machines with loose access to a promise oracle → OracleTM (work and query tape, one step per query, time |w|^k + k with every oracle), correct with every language consistent with the oracle, repeated queries allowed; reason: the paper's own form of loose access for deterministic machines (p.21); a standard machine model, polynomially equivalent to the others; the paper's assumption that machines never repeat a query (p.21) changes no class when the oracle is a fixed language
--   - encoding: binary strings, lengths polynomial in n (polynomials nondecreasing and at least 1, p.20), polynomial-time predicates on tuples → List Bool, lengths p.eval n for p : Polynomial ℕ (p ≥ 1 imposed only in L₂^P, OL₂^P and OMIN), predicates on u₁#⋯#u_k decided by the published CookPvsNP Turing machines; reason: Lean convention; same classes (a length polynomial with p(0) = 0 gives no new language or promise problem)
-- source:
--   Hirsch–Volkovich, The Ultimate Karp–Lipton Collapse, STOC 2027 submission (manuscript sha256 aca09a2b…), Theorem A.3.5 (part (2) of Theorem 4), p.27

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_KarpLiptonOM_OGTD
import Definitions.Def_KarpLiptonOM_prMA
import Definitions.Def_KarpLiptonOM_OLP2

namespace KarpLiptonOM

/-- Theorem A.3.5 (part (2) of Theorem 4, p.27): `OGTD[prMA] ⊆ OL₂^P`.

Source: Hirsch–Volkovich, *The Ultimate Karp–Lipton Collapse*, STOC 2027 submission manuscript (sha256 aca09a2b…7c62fd1b).

**Formalization Note** Strings, machines and classes are those of the `KarpLiptonOM` definitions: oracle access through every language consistent with the oracle, lengths `Polynomial ℕ`, polynomial-time predicates decided by the published `CookPvsNP` machines. The item's natural-language statement lists every difference from the page. -/
theorem theorem_A_3_5 : OGTD {PP | prMA PP} Set.univ ⊆ OLP2 := by sorry

end KarpLiptonOM
