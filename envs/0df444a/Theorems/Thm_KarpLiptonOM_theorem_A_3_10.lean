-- Prove2me | Theorems.Thm_KarpLiptonOM_theorem_A_3_10
-- name    : KarpLiptonOM.theorem_A_3_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:49:01.769182+00:00
-- url     : https://prove2.me/theorems/8a2bb6db-0df2-4227-b140-ee1cfbbe3f2e
-- title:
--   Theorem A.3.10 (transfer principle) — $\mathrm{PH}\subseteq\mathrm P^{\mathcal C}$ transfers to $\mathrm{PH}\subseteq\mathrm{OGTD}[\mathcal C]$
-- statement:
--   Let $\mathcal C$ be a class of promise problems (possibly languages) such that $\mathrm{NP} \subseteq \mathrm{P/poly}$ implies $\mathrm{PH} \subseteq \mathrm P^{\mathcal C}$. Then $\mathrm{NP} \subseteq \mathrm{P/poly}$ implies
--   $$
--   \mathrm{PH} \subseteq \mathrm{OGTD}[\mathcal C] .
--   $$
--
--   Every Karp–Lipton collapse to a class $\mathrm P^{\mathcal C}$ thus becomes a collapse to languages whose polynomial-size circuits are constructible from $1^n$ with a $\mathcal C$ oracle.
--
--   Differences from the source:
--   - encoding: deterministic polynomial-time oracle machines with loose access to a promise oracle → OracleTM (work and query tape, one step per query, time |w|^k + k with every oracle), correct with every language consistent with the oracle, repeated queries allowed; reason: the paper's own form of loose access for deterministic machines (p.21); a standard machine model, polynomially equivalent to the others; the paper's assumption that machines never repeat a query (p.21) changes no class when the oracle is a fixed language
--   - encoding: binary strings, lengths polynomial in n (polynomials nondecreasing and at least 1, p.20), polynomial-time predicates on tuples → List Bool, lengths p.eval n for p : Polynomial ℕ (p ≥ 1 imposed only in L₂^P, OL₂^P and OMIN), predicates on u₁#⋯#u_k decided by the published CookPvsNP Turing machines; reason: Lean convention; same classes (a length polynomial with p(0) = 0 gives no new language or promise problem)
--   - reading: PH, Σ_k^P, NP and P/poly used without definition → PH = ⋃_{k≥1} Σ_k^P with Σ_k^P by alternating quantifiers; NP = CookPvsNP.NP Bool; P/poly in advice form; reason: standard definitions; P/poly in the paper's own form OGTD[poly, ∗, P] (p.24)
-- source:
--   Hirsch–Volkovich, The Ultimate Karp–Lipton Collapse, STOC 2027 submission (manuscript sha256 aca09a2b…), Theorem A.3.10, p.28

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_KarpLiptonOM_PH
import Definitions.Def_KarpLiptonOM_Ppoly
import Definitions.Def_KarpLiptonOM_PC
import Definitions.Def_KarpLiptonOM_OGTD

namespace KarpLiptonOM

/-- Theorem A.3.10 (transfer principle, p.28): if `NP ⊆ P/poly` implies `PH ⊆ P^C` for a class `C` of promise problems, then `NP ⊆ P/poly` implies `PH ⊆ OGTD[C]`.

Source: Hirsch–Volkovich, *The Ultimate Karp–Lipton Collapse*, STOC 2027 submission manuscript (sha256 aca09a2b…7c62fd1b).

**Formalization Note** Strings, machines and classes are those of the `KarpLiptonOM` definitions: oracle access through every language consistent with the oracle, lengths `Polynomial ℕ`, polynomial-time predicates decided by the published `CookPvsNP` machines. The item's natural-language statement lists every difference from the page. -/
theorem theorem_A_3_10 (C : Set PromiseProblem) (hC : CookPvsNP.NP Bool ⊆ Ppoly → PH ⊆ PC C)
    (hNP : CookPvsNP.NP Bool ⊆ Ppoly) : PH ⊆ OGTD C Set.univ := by sorry

end KarpLiptonOM
