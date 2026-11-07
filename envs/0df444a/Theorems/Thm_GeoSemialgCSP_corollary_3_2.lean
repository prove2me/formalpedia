-- Prove2me | Theorems.Thm_GeoSemialgCSP_corollary_3_2
-- name    : GeoSemialgCSP.corollary_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:52:48.901097+00:00
-- url     : https://prove2.me/theorems/27cea204-b1fc-4d5b-9471-2b60dfa6b939
-- title:
--   Corollary 3.2 — every geometric semialgebraic CSP is approximation resistant
-- statement:
--   Let $P$ be a $k$-ary predicate on $\mathbb R^d$, $k\ge2$, that is semialgebraic, geometric (Definition 1.1) and satisfiable, with $\alpha^*_P<1$, where
--   $$\alpha^*_P=\sup_\mu\mathbb E_{X_1,\dots,X_k\sim\mu\ \mathrm{iid}}P(X_1,\dots,X_k)$$
--   over finitely supported distributions $\mu$ on $\mathbb R^d$. Assume the Unique Games Conjecture. Then $P$ is approximation resistant against the best biased random assignment, in the gap sense of Theorem 6.1: for every $\varepsilon_{\mathrm{comp}},\delta>0$ with $\alpha^*_P+\delta<1-\varepsilon_{\mathrm{comp}}$ it is NP-hard to distinguish instances of $\mathrm{CSP}(P)$ with
--   $$\mathrm{OPT}\ \ge\ 1-\varepsilon_{\mathrm{comp}}\qquad\text{from instances with}\qquad\mathrm{OPT}\ \le\ \alpha^*_P+\delta ,$$
--   even on instances that use distinct variables within each constraint.
--
--   This is the main result of the paper: no polynomial-time algorithm beats the best biased random assignment by a constant on a geometric semialgebraic CSP, unless the Unique Games Conjecture fails or P = NP.
--
--   Differences from the source:
--   - encoding: the Unique Games Conjecture of Khot (KKMO07, §3) → the published OptInapprox.MaxCut.UGC; reason: the same conjecture: for all η, γ > 0 some alphabet size makes the 1 − η vs γ gap NP-hard
--   - encoding: a predicate P : (ℝ^d)^k → {0,1}, semialgebraic in the k·d coordinates → its accepting set S ⊆ (EuclideanSpace ℝ (Fin d))^k, semialgebraic through finProdFinEquiv; reason: the same predicate; P(x) = 1 iff x ∈ S
--   - encoding: weighted CSP instances, made unweighted at the end of the proof (p.19) → constraint lists with multiplicity, encoded in unary (encInst); reason: the paper's final instances are unweighted with parallel copies
--   - reading: the instances can be required to use distinct variables within each constraint → distinct variables and a nonempty constraint list in both promise sets; reason: the stronger reading: hardness on the restricted promise implies hardness on the unrestricted one
--   - encoding: satisfiable → S.Nonempty; reason: the definition (footnote 1, p.1)
-- source:
--   Arvanitakis, Chatziafratis, Makarychev, Hardness of Approximation for Semialgebraic CSPs, manuscript (STOC 2027 submission, held version sha256 ee702c42…), Corollary 3.2, p.9 (PDF p.10), in the gap sense of Theorem 6.1, p.19 (PDF p.20)

import Mathlib
import Definitions.Def_OptInapprox_MaxCut_UGC
import Definitions.Def_GeoSemialgCSP_E
import Definitions.Def_GeoSemialgCSP_IsSemialgebraicPred
import Definitions.Def_GeoSemialgCSP_IsGeometric
import Definitions.Def_GeoSemialgCSP_alphaStar
import Definitions.Def_GeoSemialgCSP_encInst
import Definitions.Def_GeoSemialgCSP_YesInst
import Definitions.Def_GeoSemialgCSP_NoInst

namespace GeoSemialgCSP

/-- **Corollary 3.2 (every geometric semialgebraic CSP is approximation resistant).** Arvanitakis, Chatziafratis, Makarychev, *Hardness of Approximation for Semialgebraic CSPs*,
manuscript (STOC 2027 submission, held version sha256 ee702c42…),
Corollary 3.2, printed p.9 (PDF p.10): assuming the Unique Games Conjecture, every satisfiable
geometric semialgebraic predicate with `α*_P < 1` is approximation resistant against the best
biased random assignment, in the gap sense of Theorem 6.1 (printed p.19, PDF p.20): for every
`ε_comp, δ > 0` with `α*_P + δ < 1 − ε_comp` it is NP-hard to distinguish instances of value at
least `1 − ε_comp` from instances of value at most `α*_P + δ`, even on instances with distinct
variables in each constraint.

**Formalization Note.** The domain is `X = ℝ^d`. "Satisfiable" is `S.Nonempty` (footnote 1, p.1).
`k ≥ 2` is the §3 setup. The UGC is the published `OptInapprox.MaxCut.UGC`. Both promise sets
require a nonempty constraint list and distinct variables in each constraint. -/
theorem corollary_3_2 (hUGC : OptInapprox.MaxCut.UGC) {k d : ℕ} (hk : 2 ≤ k)
    (S : Set (Fin k → E d)) (hsa : IsSemialgebraicPred S) (hgeo : IsGeometric S)
    (hne : S.Nonempty) (hα : alphaStar Set.univ S < 1) (εc δ : ℝ) (hεc : 0 < εc) (hδ : 0 < δ)
    (hgap : alphaStar Set.univ S + δ < 1 - εc) :
    OptInapprox.MaxCut.GapNPHard (encInst (k := k)) (YesInst Set.univ S εc)
      (NoInst Set.univ S (alphaStar Set.univ S + δ)) := by sorry

end GeoSemialgCSP
