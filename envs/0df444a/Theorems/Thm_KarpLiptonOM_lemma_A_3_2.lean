-- Prove2me | Theorems.Thm_KarpLiptonOM_lemma_A_3_2
-- name    : KarpLiptonOM.lemma_A_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:49:17.086389+00:00
-- url     : https://prove2.me/theorems/2581c979-0bf1-4412-a4ba-13445c8f2796
-- title:
--   Lemma A.3.2 — $\mathrm P^T \subseteq \mathrm{OMIN}$ for a tally $T \in \mathrm L^{\mathrm P}_2$
-- statement:
--   If $T$ is a tally language in $\mathrm L^{\mathrm P}_2$, then
--   $$
--   \mathrm P^T \subseteq \mathrm{OMIN} .
--   $$
--
--   Tally languages make linear orders oblivious: on inputs of length $n$ only the instances $1^0, \dots, 1^{q(n)}$ of $T$ can be queried, and these are known in advance. This is the step from $\mathrm L^{\mathrm P}_2$ oracles to the input-oblivious class OMIN.
--
--   Differences from the source:
--   - encoding: deterministic polynomial-time oracle machines with loose access to a promise oracle → OracleTM (work and query tape, one step per query, time |w|^k + k with every oracle), correct with every language consistent with the oracle, repeated queries allowed; reason: the paper's own form of loose access for deterministic machines (p.21); a standard machine model, polynomially equivalent to the others; the paper's assumption that machines never repeat a query (p.21) changes no class when the oracle is a fixed language
--   - encoding: binary strings, lengths polynomial in n (polynomials nondecreasing and at least 1, p.20), polynomial-time predicates on tuples → List Bool, lengths p.eval n for p : Polynomial ℕ (p ≥ 1 imposed only in L₂^P, OL₂^P and OMIN), predicates on u₁#⋯#u_k decided by the published CookPvsNP Turing machines; reason: Lean convention; same classes (a length polynomial with p(0) = 0 gives no new language or promise problem)
-- source:
--   Hirsch–Volkovich, The Ultimate Karp–Lipton Collapse, STOC 2027 submission (manuscript sha256 aca09a2b…), Lemma A.3.2, p.25

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_KarpLiptonOM_LP2
import Definitions.Def_KarpLiptonOM_OMIN
import Definitions.Def_KarpLiptonOM_InP
import Definitions.Def_KarpLiptonOM_IsTally
import Definitions.Def_KarpLiptonOM_toPromise

namespace KarpLiptonOM

/-- Lemma A.3.2 (p.25): if `T` is a tally language in `L₂^P`, then `P^T ⊆ OMIN`.

Source: Hirsch–Volkovich, *The Ultimate Karp–Lipton Collapse*, STOC 2027 submission manuscript (sha256 aca09a2b…7c62fd1b).

**Formalization Note** Strings, machines and classes are those of the `KarpLiptonOM` definitions: oracle access through every language consistent with the oracle, lengths `Polynomial ℕ`, polynomial-time predicates decided by the published `CookPvsNP` machines. The item's natural-language statement lists every difference from the page. -/
theorem lemma_A_3_2 (T : Set (List Bool)) (hT : IsTally T) (hTL : T ∈ LP2)
    (L : Set (List Bool)) (hL : InP (toPromise T) L) : L ∈ OMIN := by sorry

end KarpLiptonOM
