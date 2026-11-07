-- Prove2me | Theorems.Thm_KarpLiptonOM_lemma_A_3_8
-- name    : KarpLiptonOM.lemma_A_3_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:42:10.369192+00:00
-- url     : https://prove2.me/theorems/a32699c2-0cad-44e2-a0c5-65750fa108d2
-- title:
--   Lemma A.3.8 (folklore, cf. [KL80]) — $\mathrm{NP}\subseteq\mathrm{P/poly}$ implies $\mathrm{PH}\subseteq\mathrm{P/poly}$
-- statement:
--   If $\mathrm{NP} \subseteq \mathrm{P/poly}$, then
--   $$
--   \mathrm{PH} \subseteq \mathrm{P/poly} .
--   $$
--
--   Polynomial-size circuits for NP propagate up the hierarchy level by level. The lemma provides the circuits whose canonical (lexicographically first) versions are computed in Lemma A.3.9.
--
--   Differences from the source:
--   - encoding: binary strings, lengths polynomial in n (polynomials nondecreasing and at least 1, p.20), polynomial-time predicates on tuples → List Bool, lengths p.eval n for p : Polynomial ℕ (p ≥ 1 imposed only in L₂^P, OL₂^P and OMIN), predicates on u₁#⋯#u_k decided by the published CookPvsNP Turing machines; reason: Lean convention; same classes (a length polynomial with p(0) = 0 gives no new language or promise problem)
--   - reading: PH, Σ_k^P, NP and P/poly used without definition → PH = ⋃_{k≥1} Σ_k^P with Σ_k^P by alternating quantifiers; NP = CookPvsNP.NP Bool; P/poly in advice form; reason: standard definitions; P/poly in the paper's own form OGTD[poly, ∗, P] (p.24)
-- source:
--   Hirsch–Volkovich, The Ultimate Karp–Lipton Collapse, STOC 2027 submission (manuscript sha256 aca09a2b…), Lemma A.3.8 (folklore, cf. [KL80]), p.27

import Mathlib
import Definitions.Def_CookPvsNP_defs
import Definitions.Def_KarpLiptonOM_PH
import Definitions.Def_KarpLiptonOM_Ppoly

namespace KarpLiptonOM

/-- Lemma A.3.8 (folklore, cf. [KL80]; p.27): if `NP ⊆ P/poly`, then `PH ⊆ P/poly`.

Source: Hirsch–Volkovich, *The Ultimate Karp–Lipton Collapse*, STOC 2027 submission manuscript (sha256 aca09a2b…7c62fd1b).

**Formalization Note** Strings, machines and classes are those of the `KarpLiptonOM` definitions: oracle access through every language consistent with the oracle, lengths `Polynomial ℕ`, polynomial-time predicates decided by the published `CookPvsNP` machines. The item's natural-language statement lists every difference from the page. -/
theorem lemma_A_3_8 (hNP : CookPvsNP.NP Bool ⊆ Ppoly) : PH ⊆ Ppoly := by sorry

end KarpLiptonOM
