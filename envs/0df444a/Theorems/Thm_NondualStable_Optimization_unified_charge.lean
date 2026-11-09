-- Prove2me | Theorems.Thm_NondualStable_Optimization_unified_charge
-- name    : NondualStable.Optimization.unified_charge
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:42:49.922763+00:00
-- url     : https://prove2.me/theorems/9654a668-9189-4ff2-a888-7b5a262b4163
-- title:
--   Lemma 22 — Unified charge and value budget
-- statement:
--   For every admissible $p,q$, dimension $d\ge1$, positive radius $R$, integer horizon $H\ge1$, and nested compact convex nonempty requests $K^0\supseteq\cdots\supseteq K^H\subseteq R B_p^d$, use the parameters, optimizers $u^t(g),v^t(g)$ and value increments $\Delta^t(g)$ of (10)–(14) and (27)–(28). A universal $C>0$ exists such that, with $c=e^{-2}/2$, every $g\in\mathbb R^d$ satisfies
--   $$\frac{r-1}{2}\sum_{t<H}\|v^{t+1}(g)-v^t(g)\|_r^2+\frac{c\mu}{L_d}\sum_{t<H}\|u^{t+1}(g)-u^t(g)\|_1^2\le\sum_{t<H}\Delta^t(g)\le R_r^2+2\eta R_1\|g\|_\infty.$$
--   Every increment is nonnegative. For standard Gaussian $Z$,
--   $$\mathbb E\sum_{t<H}\Delta^t(Z)\le\left[\mathbb E\left(\sum_{t<H}\Delta^t(Z)\right)^2\right]^{1/2}\le C R_r^2.$$
--   Optimizer uniqueness, measurability, sample integrability, center feasibility and both displayed moment integrabilities are conclusions. The pathwise charge and second-moment bounds are both retained; neither is replaced by an expected first-moment inequality.
--
--   Differences from the source:
--   - encoding: real coordinate vectors and exponents in [1,∞] → Fin d → ℝ and extended nonnegative exponents, using the published PiLp norm and reciprocal infinity equal to zero; reason: the same finite-dimensional norms, closed balls and endpoint cases
--   - encoding: uniform O or Õ bounds → positive constants and finite natural logarithmic or polynomial degrees quantified before every instance parameter; reason: this expands the uniform asymptotics in Section 2 and the quantitative bounds in Appendices E–G
--   - encoding: some universal positive head-charge constant c → the witness c=exp(-2)/2 from Fact 17; reason: the proof of Lemma 22 obtains precisely this lower Bregman charge
--   - encoding: the optimizers, expectations and Gaussian center of Section 5 → well-definedness and integrability are explicit conclusions alongside nonnegative increments; reason: these are the mathematical prerequisites of the displayed source formulas, established without assuming proof conclusions
-- source:
--   David Martínez-Rubio, Cristóbal Guzmán, STOC 2027 submission #415 (October 2026), printed p. 21/PDF p. 22, Lemma 22; printed p. 15/PDF p. 16, Fact 17; printed pp. 9–10/PDF pp. 10–11, (10)–(14)

import Definitions.Def_NondualStable_Optimization_GaussianCenter
open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace NondualStable.Optimization

/-- Lemma 22, printed p.21 / PDF p.22. The concrete head constant
comes from Fact 17. Both the pathwise and L2 budgets are conclusions. -/
theorem unified_charge :
    ∃ C : ℝ, 0 < C ∧ ∀ (p q : ℝ≥0∞), admissible p q →
      ∀ (d H : ℕ), 0 < d → 1 ≤ H → ∀ R : ℝ, 0 < R →
      ∀ K : ℕ → Set (Vec d), Nested p R H K →
      (∀ t ≤ H, CenterWellDefined p q R H (K t)) ∧
      (∀ g : Vec d,
        (∀ t < H, 0 ≤ increment p q R H K t g) ∧
        ((tailExponent q).toReal - 1) / 2 *
          (∑ t ∈ Finset.range H, (lpNorm (tailExponent q)
            ((optimizer p q R H (K (t + 1)) g).2 - (optimizer p q R H (K t) g).2)) ^ 2) +
        (Real.exp (-2) / 2) * mu p q R H / L d *
          (∑ t ∈ Finset.range H, (lpNorm 1
            ((optimizer p q R H (K (t + 1)) g).1 - (optimizer p q R H (K t) g).1)) ^ 2)
          ≤ totalIncrement p q R H K g ∧
        totalIncrement p q R H K g ≤ (radius p (tailExponent q) R H) ^ 2 +
          2 * eta p q d R H * radius p 1 R H * lpNorm ⊤ g) ∧
      Integrable (totalIncrement p q R H K) (gaussian d) ∧
      Integrable (fun g => (totalIncrement p q R H K g) ^ 2) (gaussian d) ∧
      (∫ g, totalIncrement p q R H K g ∂gaussian d) ≤
        Real.sqrt (∫ g, (totalIncrement p q R H K g) ^ 2 ∂gaussian d) ∧
      Real.sqrt (∫ g, (totalIncrement p q R H K g) ^ 2 ∂gaussian d) ≤
        C * (radius p (tailExponent q) R H) ^ 2 := by sorry

end NondualStable.Optimization
