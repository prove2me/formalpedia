-- Prove2me | Theorems.Thm_KarpLiptonOM_corollary_A_3_11
-- name    : KarpLiptonOM.corollary_A_3_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:49:09.068926+00:00
-- url     : https://prove2.me/theorems/fdd9d3e1-4483-4785-8449-67ffa4bbd897
-- title:
--   Corollary A.3.11 (Theorem 2) — $\mathrm{NP}\subseteq\mathrm{P/poly}$ implies $\mathrm{PH}=\mathrm{OGTD}[\mathrm{prMA}]=\mathrm{OL}^{\mathrm P}_2=\mathrm{OMIN}$
-- statement:
--   If $\mathrm{NP} \subseteq \mathrm{P/poly}$, then
--   $$
--   \mathrm{PH} = \mathrm{OGTD}[\mathrm{prMA}] = \mathrm{OL}^{\mathrm P}_2 = \mathrm{OMIN} .
--   $$
--   Consequently, every class $\mathcal D$ with $\mathrm{OGTD}[\mathrm{prMA}] \subseteq \mathcal D \subseteq \mathrm{PH}$ equals $\mathrm{PH}$.
--
--   This is the collapse to OMIN (Theorem 2 of the main text), the main ingredient of the ultimate collapse.
--
--   Differences from the source:
--   - encoding: deterministic polynomial-time oracle machines with loose access to a promise oracle → OracleTM (work and query tape, one step per query, time |w|^k + k with every oracle), correct with every language consistent with the oracle, repeated queries allowed; reason: the paper's own form of loose access for deterministic machines (p.21); a standard machine model, polynomially equivalent to the others; the paper's assumption that machines never repeat a query (p.21) changes no class when the oracle is a fixed language
--   - encoding: binary strings, lengths polynomial in n (polynomials nondecreasing and at least 1, p.20), polynomial-time predicates on tuples → List Bool, lengths p.eval n for p : Polynomial ℕ (p ≥ 1 imposed only in L₂^P, OL₂^P and OMIN), predicates on u₁#⋯#u_k decided by the published CookPvsNP Turing machines; reason: Lean convention; same classes (a length polynomial with p(0) = 0 gives no new language or promise problem)
--   - reading: PH, Σ_k^P, NP and P/poly used without definition → PH = ⋃_{k≥1} Σ_k^P with Σ_k^P by alternating quantifiers; NP = CookPvsNP.NP Bool; P/poly in advice form; reason: standard definitions; P/poly in the paper's own form OGTD[poly, ∗, P] (p.24)
--   - reading: the closing sentence "This includes all classes of Figure A.2." → not stated; reason: it names examples of D (S₂^P, P^prSBP, OP₂, …) whose position between OGTD[prMA] and PH is Theorems 3 and 4(3), outside this mission and not defined here; the corollary's claim about every such D is stated in full
-- source:
--   Hirsch–Volkovich, The Ultimate Karp–Lipton Collapse, STOC 2027 submission (manuscript sha256 aca09a2b…), Corollary A.3.11 (Theorem 2), p.28

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_KarpLiptonOM_PH
import Definitions.Def_KarpLiptonOM_Ppoly
import Definitions.Def_KarpLiptonOM_OGTD
import Definitions.Def_KarpLiptonOM_prMA
import Definitions.Def_KarpLiptonOM_OLP2
import Definitions.Def_KarpLiptonOM_OMIN

namespace KarpLiptonOM

/-- Corollary A.3.11 (Theorem 2, p.28): if `NP ⊆ P/poly`, then `PH = OGTD[prMA] = OL₂^P = OMIN`; consequently every class `D` with `OGTD[prMA] ⊆ D ⊆ PH` equals `PH`.

Source: Hirsch–Volkovich, *The Ultimate Karp–Lipton Collapse*, STOC 2027 submission manuscript (sha256 aca09a2b…7c62fd1b).

**Formalization Note** Strings, machines and classes are those of the `KarpLiptonOM` definitions: oracle access through every language consistent with the oracle, lengths `Polynomial ℕ`, polynomial-time predicates decided by the published `CookPvsNP` machines. The item's natural-language statement lists every difference from the page. -/
theorem corollary_A_3_11 (hNP : CookPvsNP.NP Bool ⊆ Ppoly) :
    PH = OGTD {PP | prMA PP} Set.univ ∧ OGTD {PP | prMA PP} Set.univ = OLP2 ∧ OLP2 = OMIN ∧
      ∀ D : Set (Set (List Bool)), OGTD {PP | prMA PP} Set.univ ⊆ D → D ⊆ PH → D = PH := by sorry

end KarpLiptonOM
