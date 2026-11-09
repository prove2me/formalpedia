-- Prove2me | Theorems.Thm_NondualStable_Optimization_deep_cut
-- name    : NondualStable.Optimization.deep_cut
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:43:08.973733+00:00
-- url     : https://prove2.me/theorems/3c24422d-f4db-4b63-93c6-16e0b4138308
-- title:
--   Lemma 4 — A null step is a deep cut
-- statement:
--   Let a phase have positive gap $\Gamma$, lower and upper levels $h^-=\ell_0+\Gamma/4$ and $h^+=\ell_0+3\Gamma/4$. Let a feasible query $z$ of a globally convex, $G$-Lipschitz objective in $\ell_q$ return a valid bounded nonzero subgradient $g$, and suppose $f(z)>h^+$. Then the halfspace is taken in the whole coordinate space and satisfies
--   $$\operatorname{dist}_q\bigl(z,\{x:f(z)+\langle g,x-z\rangle\le h^-\}\bigr)=\frac{f(z)-h^-}{\|g\|_{q^*}}\ge\frac{\Gamma}{2G}.$$
--   Distance uses a nonnegative extended-real infimum, with distance to the empty set equal to infinity. Both the exact equality and the quantitative lower bound are retained. This is the geometric null-step separation used by the reduction.
--
--   Differences from the source:
--   - encoding: real coordinate vectors and exponents in [1,∞] → Fin d → ℝ and extended nonnegative exponents, using the published PiLp norm and reciprocal infinity equal to zero; reason: the same finite-dimensional norms, closed balls and endpoint cases
--   - encoding: distance defined by an infimum with infimum of empty set equal to infinity → an ENNReal infimum over the full halfspace and ofReal of the finite quotient; reason: g is explicitly nonzero and the norm denominator is consequently positive
--   - generalization: a phase reached during Algorithm 1 → any bundle state with a positive frozen phase gap and the same valid oracle answer; reason: the distance calculation only uses the stated levels, the nonzero bounded normal and the null-step inequality; every reached phase specializes
-- source:
--   David Martínez-Rubio, Cristóbal Guzmán, STOC 2027 submission #415 (October 2026), printed p. 7/PDF p. 8, Lemma 4; proof printed p. 19/PDF p. 20

import Definitions.Def_NondualStable_Optimization_Bundle
open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace NondualStable.Optimization

/-- Lemma 4, printed p.7 / PDF p.8. The infimum is in ENNReal,
so the source convention dist(x,empty)=infinity is preserved. -/
theorem deep_cut (d : ℕ) (hd : 0 < d) (p q : ℝ≥0∞)
    (hp : 1 ≤ p) (hpq : p ≤ q) (G R : ℝ) (hG : 0 < G) (hR : 0 < R)
    (f : Vec d → ℝ) (hf : Objective q G f) (O : Oracle d)
    (hO : ValidOracle p q G R f O) (s : BundleState d)
    (hgap : 0 < (activePhase s).gap) (z : Vec d) (hz : z ∈ ball p R)
    (hnull : high (activePhase s) < f z) (hg : (O s.history z).grad ≠ 0) :
    (⨅ x : {x : Vec d // f z + dotProduct (O s.history z).grad (x - z) ≤ low (activePhase s)},
      ENNReal.ofReal (lpNorm q (z - x.val))) =
        ENNReal.ofReal ((f z - low (activePhase s)) / lpNorm (dual q) (O s.history z).grad) ∧
    (activePhase s).gap / (2 * G) ≤
      (f z - low (activePhase s)) / lpNorm (dual q) (O s.history z).grad := by sorry

end NondualStable.Optimization
