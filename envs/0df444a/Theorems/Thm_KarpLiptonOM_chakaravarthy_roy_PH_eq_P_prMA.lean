-- Prove2me | Theorems.Thm_KarpLiptonOM_chakaravarthy_roy_PH_eq_P_prMA
-- name    : KarpLiptonOM.chakaravarthy_roy_PH_eq_P_prMA
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:50:04.884142+00:00
-- url     : https://prove2.me/theorems/52f34791-4bfa-44a2-bc70-ae8eaa7f81d0
-- title:
--   [CR11] (cited) — $\mathrm{NP}\subseteq\mathrm{P/poly}$ implies $\mathrm{PH} = \mathrm P^{\mathrm{prMA}}$
-- statement:
--   The Karp–Lipton collapse of Chakaravarthy and Roy [CR11], as cited in the proof of Corollary A.3.11: if $\mathrm{NP} \subseteq \mathrm{P/poly}$, then
--   $$
--   \mathrm{PH} = \mathrm P^{\mathrm{prMA}} ,
--   $$
--   with loose access to the prMA oracle.
--
--   Combined with the transfer principle (Theorem A.3.10) it gives $\mathrm{PH} \subseteq \mathrm{OGTD}[\mathrm{prMA}]$, the first step of the collapse to OMIN.
--
--   Differences from the source:
--   - encoding: deterministic polynomial-time oracle machines with loose access to a promise oracle → OracleTM (work and query tape, one step per query, time |w|^k + k with every oracle), correct with every language consistent with the oracle, repeated queries allowed; reason: the paper's own form of loose access for deterministic machines (p.21); a standard machine model, polynomially equivalent to the others; the paper's assumption that machines never repeat a query (p.21) changes no class when the oracle is a fixed language
--   - encoding: binary strings, lengths polynomial in n (polynomials nondecreasing and at least 1, p.20), polynomial-time predicates on tuples → List Bool, lengths p.eval n for p : Polynomial ℕ (p ≥ 1 imposed only in L₂^P, OL₂^P and OMIN), predicates on u₁#⋯#u_k decided by the published CookPvsNP Turing machines; reason: Lean convention; same classes (a length polynomial with p(0) = 0 gives no new language or promise problem)
--   - reading: PH, Σ_k^P, NP and P/poly used without definition → PH = ⋃_{k≥1} Σ_k^P with Σ_k^P by alternating quantifiers; NP = CookPvsNP.NP Bool; P/poly in advice form; reason: standard definitions; P/poly in the paper's own form OGTD[poly, ∗, P] (p.24)
-- source:
--   Hirsch–Volkovich, The Ultimate Karp–Lipton Collapse, STOC 2027 submission (manuscript sha256 aca09a2b…), proof of Corollary A.3.11, p.28 (cited: [CR11]; again in the proof of Lemma A.4.2, p.30)

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_KarpLiptonOM_PH
import Definitions.Def_KarpLiptonOM_Ppoly
import Definitions.Def_KarpLiptonOM_PC
import Definitions.Def_KarpLiptonOM_prMA

namespace KarpLiptonOM

/-- [CR11] (Chakaravarthy–Roy, as cited in the proof of Corollary A.3.11, p.28): if `NP ⊆ P/poly`, then `PH = P^prMA`.

Source: Hirsch–Volkovich, *The Ultimate Karp–Lipton Collapse*, STOC 2027 submission manuscript (sha256 aca09a2b…7c62fd1b).

**Formalization Note** Strings, machines and classes are those of the `KarpLiptonOM` definitions: oracle access through every language consistent with the oracle, lengths `Polynomial ℕ`, polynomial-time predicates decided by the published `CookPvsNP` machines. The item's natural-language statement lists every difference from the page. -/
theorem chakaravarthy_roy_PH_eq_P_prMA (hNP : CookPvsNP.NP Bool ⊆ Ppoly) :
    PH = PC {PP | prMA PP} := by sorry

end KarpLiptonOM
