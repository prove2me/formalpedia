-- Prove2me | Theorems.Thm_GeoSemialgCSP_theorem_6_1
-- name    : GeoSemialgCSP.theorem_6_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:52:31.728842+00:00
-- url     : https://prove2.me/theorems/a7735f0e-367f-4411-bdca-c7bd3f7d6757
-- title:
--   Theorem 6.1 — hardness from cousins embeddings
-- statement:
--   Let $k\ge2$, $X\subseteq\mathbb R^d$ (no further assumption on $X$), and let $P$ be the restriction to $X^k$ of a fixed semialgebraic predicate $S$ on $(\mathbb R^d)^k$ satisfying property (2). If $\alpha^*_P<1$, then, assuming the Unique Games Conjecture, for every $\varepsilon_{\mathrm{comp}},\delta>0$ with $\alpha^*_P+\delta<1-\varepsilon_{\mathrm{comp}}$ it is NP-hard to distinguish CSP instances with
--   $$\mathrm{OPT}\ \ge\ 1-\varepsilon_{\mathrm{comp}}\qquad\text{from instances with}\qquad\mathrm{OPT}\ \le\ \alpha^*_P+\delta ,$$
--   where assignments take values in $X$ and $\alpha^*_P$ is the best biased random assignment on $X$. The instances can be required to use distinct variables within each constraint.
--
--   This is the paper's general hardness theorem; it also recovers the known approximation resistance of ordering and phylogenetic CSPs.
--
--   Differences from the source:
--   - encoding: the Unique Games Conjecture of Khot (KKMO07, §3) → the published OptInapprox.MaxCut.UGC; reason: the same conjecture: for all η, γ > 0 some alphabet size makes the 1 − η vs γ gap NP-hard
--   - encoding: a predicate P : (ℝ^d)^k → {0,1}, semialgebraic in the k·d coordinates → its accepting set S ⊆ (EuclideanSpace ℝ (Fin d))^k, semialgebraic through finProdFinEquiv; reason: the same predicate; P(x) = 1 iff x ∈ S
--   - generalization: property (2): a cousins homomorphism for every finite ordered k-ary tree → HasCousinsHoms: one for every complete ordered k-ary tree; reason: a weaker hypothesis: every finite ordered k-ary tree embeds in a complete one preserving cousins tuples, so the printed property implies it; the proof uses only complete trees (Lemma 4.3 item 4)
--   - encoding: weighted CSP instances, made unweighted at the end of the proof (p.19) → constraint lists with multiplicity, encoded in unary (encInst); reason: the paper's final instances are unweighted with parallel copies
--   - reading: the instances can be required to use distinct variables within each constraint → distinct variables and a nonempty constraint list in both promise sets; reason: the stronger reading: hardness on the restricted promise implies hardness on the unrestricted one
-- source:
--   Arvanitakis, Chatziafratis, Makarychev, Hardness of Approximation for Semialgebraic CSPs, manuscript (STOC 2027 submission, held version sha256 ee702c42…), Theorem 6.1, p.19 (PDF p.20)

import Mathlib
import Definitions.Def_OptInapprox_MaxCut_UGC
import Definitions.Def_GeoSemialgCSP_E
import Definitions.Def_GeoSemialgCSP_IsSemialgebraicPred
import Definitions.Def_GeoSemialgCSP_HasCousinsHoms
import Definitions.Def_GeoSemialgCSP_alphaStar
import Definitions.Def_GeoSemialgCSP_encInst
import Definitions.Def_GeoSemialgCSP_YesInst
import Definitions.Def_GeoSemialgCSP_NoInst

namespace GeoSemialgCSP

/-- **Theorem 6.1 (hardness from cousins embeddings).** Arvanitakis, Chatziafratis, Makarychev, *Hardness of Approximation for Semialgebraic CSPs*,
manuscript (STOC 2027 submission, held version sha256 ee702c42…), Theorem 6.1, printed p.19 (PDF p.20):
suppose `P` is the restriction of a fixed semialgebraic predicate to `X^k` and satisfies property
(2). If `α*_P < 1`, then, assuming the Unique Games Conjecture, for every `ε_comp, δ > 0` with
`α*_P + δ < 1 − ε_comp` it is NP-hard to distinguish CSP instances with value at least
`1 − ε_comp` from instances with value at most `α*_P + δ`; the instances can be required to use
distinct variables within each constraint.

**Formalization Note.** `S ⊆ (ℝ^d)^k` is the ambient semialgebraic predicate, assignments take
values in `X` (no assumption on `X`), and `α*_P` is over distributions on `X`. Property (2) is for
the complete trees (`HasCousinsHoms`). Both promise sets require a nonempty constraint list and
distinct variables in each constraint. Instances are unweighted constraint lists, encoded in
unary (`encInst`). -/
theorem theorem_6_1 (hUGC : OptInapprox.MaxCut.UGC) {k d : ℕ} (hk : 2 ≤ k) (X : Set (E d))
    (S : Set (Fin k → E d)) (hsa : IsSemialgebraicPred S) (hcous : HasCousinsHoms X S)
    (hα : alphaStar X S < 1) (εc δ : ℝ) (hεc : 0 < εc) (hδ : 0 < δ)
    (hgap : alphaStar X S + δ < 1 - εc) :
    OptInapprox.MaxCut.GapNPHard (encInst (k := k)) (YesInst X S εc)
      (NoInst X S (alphaStar X S + δ)) := by sorry

end GeoSemialgCSP
