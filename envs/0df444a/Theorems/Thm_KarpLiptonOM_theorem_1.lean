-- Prove2me | Theorems.Thm_KarpLiptonOM_theorem_1
-- name    : KarpLiptonOM.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:50:41.885259+00:00
-- url     : https://prove2.me/theorems/4188ae3f-e164-4eac-be28-66861dfae5ee
-- title:
--   Theorem 1 (the ultimate Karp–Lipton collapse) — $\mathrm{OUM\subseteq OM\subseteq OMIN\cap P^{sOprMA}\cap ZPP^{ONP}}$; $\mathrm{NP\subseteq P/poly\Rightarrow PH=OUM=OM}$
-- statement:
--   Let $\mathrm{OM} = \mathrm{OGTD}[\mathrm{FP}^{\mathrm{sOprMA}}, \text{co-ONP}, \mathrm P]$ be the class of languages decided by a polynomial-time generator with a strict oblivious Merlin–Arthur oracle, a co-ONP tester and a polynomial-time decoder, and $\mathrm{OUM}$ its subclass in which the tester accepts exactly one advice string per length. Then:
--
--   1. unconditionally,
--   $$
--   \mathrm{OUM} \subseteq \mathrm{OM} \subseteq \mathrm{OMIN} \cap \mathrm P^{\mathrm{sOprMA}} \cap \mathrm{ZPP}^{\mathrm{ONP}} ;
--   $$
--   2. if $\mathrm{NP} \subseteq \mathrm{P/poly}$, then
--   $$
--   \mathrm{PH} = \mathrm{OUM} = \mathrm{OM} .
--   $$
--
--   OM lies inside each of the three deepest known Karp–Lipton collapse classes, OMIN, $\mathrm P^{\mathrm{sOprMA}}$ and $\mathrm{ZPP}^{\mathrm{ONP}}$, and the polynomial hierarchy still collapses to it under $\mathrm{NP} \subseteq \mathrm{P/poly}$. Each containment comes from running the generator in a different way: with its oracle, derandomized by an oblivious linear order, or sampled with an ONP oracle and checked by the tester.
--
--   Differences from the source:
--   - encoding: deterministic polynomial-time oracle machines with loose access to a promise oracle → OracleTM (work and query tape, one step per query, time |w|^k + k with every oracle), correct with every language consistent with the oracle, repeated queries allowed; reason: the paper's own form of loose access for deterministic machines (p.21); a standard machine model, polynomially equivalent to the others; the paper's assumption that machines never repeat a query (p.21) changes no class when the oracle is a fixed language
--   - encoding: binary strings, lengths polynomial in n (polynomials nondecreasing and at least 1, p.20), polynomial-time predicates on tuples → List Bool, lengths p.eval n for p : Polynomial ℕ (p ≥ 1 imposed only in L₂^P, OL₂^P and OMIN), predicates on u₁#⋯#u_k decided by the published CookPvsNP Turing machines; reason: Lean convention; same classes (a length polynomial with p(0) = 0 gives no new language or promise problem)
--   - reading: PH, Σ_k^P, NP and P/poly used without definition → PH = ⋃_{k≥1} Σ_k^P with Σ_k^P by alternating quantifiers; NP = CookPvsNP.NP Bool; P/poly in advice form; reason: standard definitions; P/poly in the paper's own form OGTD[poly, ∗, P] (p.24)
--   - reading: ZPP^ONP used without definition → standard ZPP: output L(x) (the one-bit string [b]) or ? (any other output string), never wrong, Pr[output = L(x)] ≥ 1/2, random string a second input of length q(|x|); reason: standard definition; the proof of Theorem A.4.5 gives probability 3/4
--   - encoding: co-ONP tester, a language of pairs (1ⁿ, a) under a length-regular pair encoding (p.20) → coONP2 T: the complement of T has an ONP verifier V(u, a, w) whose oblivious witness depends on (|u|, |a|) and has length p(|u| + |a|); reason: with a length-regular encoding the encoded length and the pair of lengths determine each other, so the witnesses are the same; same class
-- source:
--   Hirsch–Volkovich, The Ultimate Karp–Lipton Collapse, STOC 2027 submission (manuscript sha256 aca09a2b…), Theorem 1, p.5 (proved as Theorems A.4.5 and A.4.6, p.31)

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_KarpLiptonOM_OM
import Definitions.Def_KarpLiptonOM_OUM
import Definitions.Def_KarpLiptonOM_OMIN
import Definitions.Def_KarpLiptonOM_PC
import Definitions.Def_KarpLiptonOM_ZPP
import Definitions.Def_KarpLiptonOM_ONP
import Definitions.Def_KarpLiptonOM_PH
import Definitions.Def_KarpLiptonOM_Ppoly

namespace KarpLiptonOM

/-- Theorem 1 (the ultimate Karp–Lipton collapse; p.5, proved as Theorems A.4.5 and A.4.6, p.31): (1) `OUM ⊆ OM ⊆ OMIN ∩ P^sOprMA ∩ ZPP^ONP`; (2) if `NP ⊆ P/poly`, then `PH = OUM = OM`.

Source: Hirsch–Volkovich, *The Ultimate Karp–Lipton Collapse*, STOC 2027 submission manuscript (sha256 aca09a2b…7c62fd1b).

**Formalization Note** Strings, machines and classes are those of the `KarpLiptonOM` definitions: oracle access through every language consistent with the oracle, lengths `Polynomial ℕ`, polynomial-time predicates decided by the published `CookPvsNP` machines. The item's natural-language statement lists every difference from the page. -/
theorem theorem_1 :
    (OUM ⊆ OM ∧ OM ⊆ OMIN ∧ OM ⊆ PC {PP | sOprMA PP} ∧ OM ⊆ {L | ∃ A ∈ ONP, ZPP A L}) ∧
    (CookPvsNP.NP Bool ⊆ Ppoly → PH = OUM ∧ OUM = OM) := by sorry

end KarpLiptonOM
