-- Prove2me | Theorems.Thm_KarpLiptonOM_lemma_A_4_2
-- name    : KarpLiptonOM.lemma_A_4_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:49:48.388483+00:00
-- url     : https://prove2.me/theorems/60842097-bf9b-414e-894a-823251da6069
-- title:
--   Lemma A.4.2 — $\mathrm{NP}\subseteq\mathrm{P/poly}$ implies $\mathrm{prMA}\subseteq\mathrm{sOprMA}$ and $\mathrm{PH}=\mathrm P^{\mathrm{sOprMA}}$
-- statement:
--   If $\mathrm{NP} \subseteq \mathrm{P/poly}$, then every promise problem in prMA belongs to sOprMA. Consequently,
--   $$
--   \mathrm{PH} = \mathrm P^{\mathrm{sOprMA}} .
--   $$
--
--   Under the hypothesis, Merlin's proof can be replaced by a circuit that finds satisfying assignments, which serves as an input-oblivious proof dominating every other proof. This collapse supplies the generator of the unique-advice class OUM.
--
--   Differences from the source:
--   - encoding: deterministic polynomial-time oracle machines with loose access to a promise oracle → OracleTM (work and query tape, one step per query, time |w|^k + k with every oracle), correct with every language consistent with the oracle, repeated queries allowed; reason: the paper's own form of loose access for deterministic machines (p.21); a standard machine model, polynomially equivalent to the others; the paper's assumption that machines never repeat a query (p.21) changes no class when the oracle is a fixed language
--   - encoding: binary strings, lengths polynomial in n (polynomials nondecreasing and at least 1, p.20), polynomial-time predicates on tuples → List Bool, lengths p.eval n for p : Polynomial ℕ (p ≥ 1 imposed only in L₂^P, OL₂^P and OMIN), predicates on u₁#⋯#u_k decided by the published CookPvsNP Turing machines; reason: Lean convention; same classes (a length polynomial with p(0) = 0 gives no new language or promise problem)
--   - reading: PH, Σ_k^P, NP and P/poly used without definition → PH = ⋃_{k≥1} Σ_k^P with Σ_k^P by alternating quantifiers; NP = CookPvsNP.NP Bool; P/poly in advice form; reason: standard definitions; P/poly in the paper's own form OGTD[poly, ∗, P] (p.24)
-- source:
--   Hirsch–Volkovich, The Ultimate Karp–Lipton Collapse, STOC 2027 submission (manuscript sha256 aca09a2b…), Lemma A.4.2, p.30

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_KarpLiptonOM_PH
import Definitions.Def_KarpLiptonOM_Ppoly
import Definitions.Def_KarpLiptonOM_prMA
import Definitions.Def_KarpLiptonOM_sOprMA
import Definitions.Def_KarpLiptonOM_PC

namespace KarpLiptonOM

/-- Lemma A.4.2 (collapse to `P^sOprMA`, p.30): if `NP ⊆ P/poly`, then every promise problem in `prMA` belongs to `sOprMA`; consequently `PH = P^sOprMA`.

Source: Hirsch–Volkovich, *The Ultimate Karp–Lipton Collapse*, STOC 2027 submission manuscript (sha256 aca09a2b…7c62fd1b).

**Formalization Note** Strings, machines and classes are those of the `KarpLiptonOM` definitions: oracle access through every language consistent with the oracle, lengths `Polynomial ℕ`, polynomial-time predicates decided by the published `CookPvsNP` machines. The item's natural-language statement lists every difference from the page. -/
theorem lemma_A_4_2 (hNP : CookPvsNP.NP Bool ⊆ Ppoly) :
    (∀ PP : PromiseProblem, prMA PP → sOprMA PP) ∧ PH = PC {PP | sOprMA PP} := by sorry

end KarpLiptonOM
