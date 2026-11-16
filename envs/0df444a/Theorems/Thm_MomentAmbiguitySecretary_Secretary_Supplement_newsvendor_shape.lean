-- Prove2me | Theorems.Thm_MomentAmbiguitySecretary_Secretary_Supplement_newsvendor_shape
-- name    : MomentAmbiguitySecretary.Secretary.Supplement.newsvendor_shape
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:53:35.260162+00:00
-- url     : https://prove2.me/theorems/3cedfa86-9e58-4dee-9ba2-7fe386757281
-- title:
--   Lemma 4.1 (used in the proof of Theorem 4.1) — Concavity, both one-sided derivatives, the derivative at zero and the full argmax characterization
-- statement:
--   Let $\beta\in[0,1]$ and let $\psi$ be any nonnegative demand law with finite first moment. Write $F(q)=\Pr(D\le q)$ and $F(q^-)=\Pr(D<q)$, and $\operatorname{Profit}(q)=\mathbb E[\min(D,q)]-(1-\beta)q$. This profit is concave on $[0,\infty)$ and
--   $$\partial_-\operatorname{Profit}(q)=\beta-F(q^-)\quad(q>0),\qquad
--   \partial_+\operatorname{Profit}(q)=\beta-F(q)\quad(q\ge0).$$
--   Its full maximizer set is
--   $$\operatorname*{argmax}_{q\ge0}\operatorname{Profit}(q)=\{q\ge0:F(q^-)\le\beta\le F(q)\}.$$
--   This includes the right derivative at zero, arbitrary atoms, and both endpoint values of $\beta$. It requires no higher demand moments.
--
--   Differences from the source: none.
-- source:
--   Cristi, Russo & Zhang (2026), Moment Ambiguity and the Limits of Robust Stochastic Optimization, STOC 2027 submission #44, supplied checksum-pinned preprint. Lemma 4.1, PDF/printed p.9; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/44.pdf; SHA-256 8759453424e009e4e0380263fc1672d9622bea438cc43904e881469f456c9895

import Definitions.Def_MomentAmbiguitySecretary_Secretary_Supplement_Newsvendor

open MeasureTheory Set Filter
open scoped NNReal ENNReal BigOperators Topology

namespace MomentAmbiguitySecretary.Secretary.Supplement

/-- Lemma 4.1, supplied preprint, PDF/printed p.9. -/
theorem newsvendor_shape (ψ : Distribution) (hψ : FiniteMean (ψ : Measure ℝ≥0))
    (β : ℝ) (hβ : β ∈ Icc 0 1) :
    ConcaveOn ℝ (Ici 0) (profit (ψ : Measure ℝ≥0) β) ∧
    (∀ q : ℝ, 0 < q →
      HasDerivWithinAt (profit (ψ : Measure ℝ≥0) β)
        (β - openCDF (ψ : Measure ℝ≥0) q) (Iic q) q) ∧
    (∀ q : ℝ, 0 ≤ q →
      HasDerivWithinAt (profit (ψ : Measure ℝ≥0) β)
        (β - closedCDF (ψ : Measure ℝ≥0) q) (Ici q) q) ∧
    optimalOrders (ψ : Measure ℝ≥0) β =
      {q | 0 ≤ q ∧ openCDF (ψ : Measure ℝ≥0) q ≤ β ∧
        β ≤ closedCDF (ψ : Measure ℝ≥0) q} := by sorry

end MomentAmbiguitySecretary.Secretary.Supplement
