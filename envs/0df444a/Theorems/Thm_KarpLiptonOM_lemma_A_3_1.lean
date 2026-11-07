-- Prove2me | Theorems.Thm_KarpLiptonOM_lemma_A_3_1
-- name    : KarpLiptonOM.lemma_A_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:48:50.923194+00:00
-- url     : https://prove2.me/theorems/15ad4f33-c5d6-4f94-b6e4-75d56d6e16a3
-- title:
--   Lemma A.3.1 — $\mathrm L^{\mathrm P}_2$ is closed under polynomial-time Turing reductions
-- statement:
--   The order-based class $\mathrm L^{\mathrm P}_2$ is closed under polynomial-time Turing reductions: if $A_1, \dots, A_r \in \mathrm L^{\mathrm P}_2$, then
--   $$
--   \mathrm P^{A_1, \dots, A_r} \subseteq \mathrm L^{\mathrm P}_2 .
--   $$
--
--   The paper proves this directly from the order-based definition (Definition A.2.7), without the reduction-based characterization of Korten–Pitassi. It is the closure step behind $\mathrm P^{\mathrm{prMA}} \subseteq \mathrm L^{\mathrm P}_2$ and the collapse to OMIN.
--
--   Differences from the source:
--   - encoding: deterministic polynomial-time oracle machines with loose access to a promise oracle → OracleTM (work and query tape, one step per query, time |w|^k + k with every oracle), correct with every language consistent with the oracle, repeated queries allowed; reason: the paper's own form of loose access for deterministic machines (p.21); a standard machine model, polynomially equivalent to the others; the paper's assumption that machines never repeat a query (p.21) changes no class when the oracle is a fixed language
--   - encoding: binary strings, lengths polynomial in n (polynomials nondecreasing and at least 1, p.20), polynomial-time predicates on tuples → List Bool, lengths p.eval n for p : Polynomial ℕ (p ≥ 1 imposed only in L₂^P, OL₂^P and OMIN), predicates on u₁#⋯#u_k decided by the published CookPvsNP Turing machines; reason: Lean convention; same classes (a length polynomial with p(0) = 0 gives no new language or promise problem)
--   - generalization: A₁, …, A_r ∈ L₂^P, r ≥ 1 implicitly → every r ∈ ℕ, including r = 0 (P ⊆ L₂^P); reason: the r = 0 case also holds; the statement specializes to every printed r ≥ 1
--   - encoding: P^{A₁,…,A_r} → P with the single oracle A₁⊕⋯⊕A_r (langJoin A); reason: the identification of the proof of Lemma A.3.1 (p.25); r = 0 gives P
-- source:
--   Hirsch–Volkovich, The Ultimate Karp–Lipton Collapse, STOC 2027 submission (manuscript sha256 aca09a2b…), Lemma A.3.1, p.25

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_KarpLiptonOM_LP2
import Definitions.Def_KarpLiptonOM_InP
import Definitions.Def_KarpLiptonOM_toPromise
import Definitions.Def_KarpLiptonOM_langJoin

namespace KarpLiptonOM

/-- Lemma A.3.1 (p.25): `L₂^P` is closed under polynomial-time Turing reductions, `P^{A₁,…,A_r} ⊆ L₂^P` for `A₁,…,A_r ∈ L₂^P`.

Source: Hirsch–Volkovich, *The Ultimate Karp–Lipton Collapse*, STOC 2027 submission manuscript (sha256 aca09a2b…7c62fd1b).

**Formalization Note** Strings, machines and classes are those of the `KarpLiptonOM` definitions: oracle access through every language consistent with the oracle, lengths `Polynomial ℕ`, polynomial-time predicates decided by the published `CookPvsNP` machines. The item's natural-language statement lists every difference from the page. -/
theorem lemma_A_3_1 (r : ℕ) (A : Fin r → Set (List Bool)) (hA : ∀ i, A i ∈ LP2)
    (L : Set (List Bool)) (hL : InP (toPromise (langJoin A)) L) : L ∈ LP2 := by sorry

end KarpLiptonOM
