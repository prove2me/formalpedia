-- Prove2me | Theorems.Thm_GeoRobustLearn_fact_5_8
-- name    : GeoRobustLearn.fact_5_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T04:07:53.692363+00:00
-- url     : https://prove2.me/theorems/2dd23467-db9e-477a-a2d3-539d842d90e7
-- title:
--   Fact 5.8 — Harnack inequality $(T_sg)(z)\le\sqrt{(T_sg^2)(x)}\,e^{\|z-x\|_2^2/(2\sigma_s^2)}$
-- statement:
--   Let $n\ge1$, $s>0$, $\sigma_s=\sqrt{1-e^{-2s}}$, and let $g:\mathbb R^n\to[0,\infty)$ be measurable. Then for all $x,z\in\mathbb R^n$,
--
--   $$(T_sg)(z)\le\sqrt{(T_sg^2)(x)}\,\exp\Big(\frac{\|z-x\|_2^2}{2\sigma_s^2}\Big).$$
--
--   This is the Harnack inequality for the Ornstein–Uhlenbeck semigroup ([Wan97, Lemma 2.1]); it turns smallness of $T_sg^2$ at one point into smallness of $T_sg$ on a ball.
--
--   Differences from the source:
--   - generalization: the standing assumption σ_s < 1/2 of §3.3 (p.14) → every s > 0; reason: the proofs (§5.4–5.10, App. D) use only σ_s ≤ 1 and ρ_s ≤ 1 (paper.md decision 10); every s with σ_s < 1/2 is covered
--   - encoding: T_s(·) and expectations of the nonnegative quantities def_F, def_F², max{0, ±W} → lower Lebesgue integrals in [0, ∞] (ouLin, ∫⁻); reason: same values whenever finite; avoids the junk value 0 of a Bochner integral
-- source:
--   Lange, Marcussen, Vasilyan, Geometrically Constrained Learning I: Agnostically Learning Adversarially Robust Classifiers, manuscript (Nov. 3, 2026; sha256 8cbf3f52…), Fact 5.8, p.24 (PDF p.24)

import Definitions.Def_GeoRobustLearn_CertDefect

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace GeoRobustLearn

open GeoLipLearn.Agnostic

/-- **Fact 5.8** (Harnack inequality for the Gaussian noise operator [Wan97, Lemma 2.1]), p.24.

Lange, Marcussen, Vasilyan, *Geometrically Constrained Learning I*, manuscript of November 3, 2026
(sha256 8cbf3f52…).

Let `n ≥ 1`, `s > 0` and let `g : ℝ^n → [0, ∞)` be measurable. Then for all `x, z ∈ ℝ^n`,
`(T_s g)(z) ≤ √((T_s g²)(x)) · exp(‖z − x‖₂² / (2σ_s²))`.

**Formalization Note.** `T_s` of a nonnegative function is `ouLin` (a lower Lebesgue integral in
`[0, ∞]`), so the inequality also holds, and means something, when `T_s g` or `T_s g²` is infinite;
the square root is `(·)^{1/2}` in `[0, ∞]`. `σ_s` is the published `sigma s`. -/
theorem fact_5_8 (n : ℕ) (hn : 1 ≤ n) (s : ℝ) (hs : 0 < s) (g : Space n → ℝ)
    (hg0 : ∀ y, 0 ≤ g y) (hg : Measurable g) (x z : Space n) :
    ouLin s g z ≤
      ouLin s (fun y => g y ^ 2) x ^ (1 / 2 : ℝ) *
        ENNReal.ofReal (Real.exp (‖z - x‖ ^ 2 / (2 * sigma s ^ 2))) := by sorry

end GeoRobustLearn
