-- Prove2me | Theorems.Thm_NondualStable_Optimization_head_tail
-- name    : NondualStable.Optimization.head_tail
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:42:17.679618+00:00
-- url     : https://prove2.me/theorems/eb6d7c81-55b3-4d2b-95d2-a60b64b6ed68
-- title:
--   Lemma 8 — Head-tail decomposition
-- statement:
--   Let $d\ge1$, let $H\ge1$ be an integer, let $1\le p\le a\le\infty$, and let $x\in R B_p^d$. Put $\tau=H^{-1/p}$ and retain in $u$ exactly the coordinates satisfying $|x_i|>R\tau$. Then
--   $$\|u\|_1\le R H^{1-1/p},\qquad \|x-u\|_a\le R H^{1/a-1/p},\qquad R B_p^d\subseteq R H^{1-1/p}B_1^d+R H^{1/a-1/p}B_a^d.$$
--   The decomposition includes $p=a=\infty$, where the head is zero. It supplies the nonempty lift used by the mixed-norm reference center.
--
--   Differences from the source:
--   - encoding: real coordinate vectors and exponents in [1,∞] → Fin d → ℝ and extended nonnegative exponents, using the published PiLp norm and reciprocal infinity equal to zero; reason: the same finite-dimensional norms, closed balls and endpoint cases
--   - encoding: Minkowski inclusion of two norm balls → every vector in the domain has a sum decomposition with each component in its specified ball; reason: the existential formulation is exactly set Minkowski addition
--   - generalization: positive radius in the standing setting → nonnegative radius including R=0; reason: the zero-radius ball contains only zero and all three conclusions remain valid
-- source:
--   David Martínez-Rubio, Cristóbal Guzmán, STOC 2027 submission #415 (October 2026), printed p. 9/PDF p. 10, Lemma 8; proof printed p. 20/PDF p. 21

import Definitions.Def_NondualStable_Optimization_Geometry
open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace NondualStable.Optimization

/-- Lemma 8, printed p.9 / PDF p.10, all exponents including p=s=infinity. -/
theorem head_tail (d H : ℕ) (hd : 0 < d) (hH : 1 ≤ H)
    (p s : ℝ≥0∞) (hp : 1 ≤ p) (hps : p ≤ s) (R : ℝ) (hR : 0 ≤ R)
    (x : Vec d) (hx : x ∈ ball p R) :
    lpNorm 1 (head p R H x) ≤ radius p 1 R H ∧
    lpNorm s (x - head p R H x) ≤ radius p s R H ∧
    ∀ y ∈ ball (d := d) p R, ∃ u ∈ ball 1 (radius p 1 R H),
      ∃ v ∈ ball s (radius p s R H), y = u + v := by sorry

end NondualStable.Optimization
