-- Prove2me | Theorems.Thm_GeoRobustLearn_proposition_5_5
-- name    : GeoRobustLearn.proposition_5_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T04:08:36.532942+00:00
-- url     : https://prove2.me/theorems/e54a00ba-9baf-49bb-a26b-1d98796a8616
-- title:
--   Proposition 5.5 — $T_s(\mathrm{def}_f^2)(x,0)\le e^{-2r^2/\sigma_s^2}$ certifies $T_sf$ on the $r$-ball around $x$
-- statement:
--   Let $d\ge1$, $f$ a polynomial on $\mathbb R^d\times\mathbb R$, $s>0$, $x\in\mathbb R^d$ and $r\ge0$. Suppose
--
--   $$T_s(\mathrm{def}_f^2)(x,0)\le e^{-2r^2/\sigma_s^2}.$$
--
--   Then:
--
--   1. $\mathrm{def}_{T_sf}(z,a)\le1$ for every $z$ with $\|z-x\|_2\le r$ and every $a\in[-r,r]$;
--   2. for every $z$ with $\|z-x\|_2\le r$, $\;(T_sf)(x,-r)-r\le(T_sf)(z,0)\le(T_sf)(x,r)+r$.
--
--   This is the pointwise certificate used to bound the boundary volume of the rounded classifier.
--
--   Differences from the source:
--   - encoding: f : ℝ^d × ℝ → ℝ a polynomial → evalPoly Q for a real polynomial Q in the d + 1 coordinates of Space (d+1), the offset a being the last coordinate; reason: Lean representation of ℝ^d × ℝ; same instances
--   - generalization: the standing assumption σ_s < 1/2 of §3.3 (p.14) → every s > 0; reason: the proofs (§5.4–5.10, App. D) use only σ_s ≤ 1 and ρ_s ≤ 1 (paper.md decision 10); every s with σ_s < 1/2 is covered
--   - encoding: T_s(·) and expectations of the nonnegative quantities def_F, def_F², max{0, ±W} → lower Lebesgue integrals in [0, ∞] (ouLin, ∫⁻); reason: same values whenever finite; avoids the junk value 0 of a Bochner integral
-- source:
--   Lange, Marcussen, Vasilyan, Geometrically Constrained Learning I: Agnostically Learning Adversarially Robust Classifiers, manuscript (Nov. 3, 2026; sha256 8cbf3f52…), Proposition 5.5, p.23 (PDF p.23)

import Definitions.Def_GeoRobustLearn_OffsetLift
import Definitions.Def_GeoRobustLearn_CertDefect

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace GeoRobustLearn

open GeoLipLearn.Agnostic

/-- **Proposition 5.5** (Certifying smallness of the defect on a ball), p.23.

Lange, Marcussen, Vasilyan, *Geometrically Constrained Learning I*, manuscript of November 3, 2026
(sha256 8cbf3f52…).

Let `d ≥ 1`, `F` a polynomial on `ℝ^d × ℝ`, `s > 0`, `x ∈ ℝ^d` and `r ≥ 0`. Suppose
`T_s(def_F²)(x, 0) ≤ e^{−2r²/σ_s²}`. Then
1. `def_{T_s F}(z, a) ≤ 1` for every `z` with `‖z − x‖₂ ≤ r` and every `a ∈ [−r, r]`;
2. for every `z` with `‖z − x‖₂ ≤ r`, `(T_s F)(x, −r) − r ≤ (T_s F)(z, 0) ≤ (T_s F)(x, r) + r`.

**Formalization Note.** `F = evalPoly Q`, `T_s F = ou s F`, `T_s(def_F²)` is `ouLin` of the
nonnegative `def_F²`, and `σ_s = sigma s > 0` since `s > 0`. -/
theorem proposition_5_5 (d : ℕ) (hd : 1 ≤ d) (Q : GeoLipLearn.Agnostic.Poly (d+1))
    (s : ℝ) (hs : 0 < s)
    (x : Space d) (r : ℝ) (hr : 0 ≤ r)
    (hcert : ouLin s (fun w => certDefect (evalPoly Q) w ^ 2) (lift x 0) ≤
      ENNReal.ofReal (Real.exp (-2 * r ^ 2 / sigma s ^ 2))) :
    (∀ z : Space d, ‖z - x‖ ≤ r → ∀ a ∈ Set.Icc (-r) r,
      certDefect (ou s (evalPoly Q)) (lift z a) ≤ 1) ∧
    (∀ z : Space d, ‖z - x‖ ≤ r →
      ou s (evalPoly Q) (lift x (-r)) - r ≤ ou s (evalPoly Q) (lift z 0) ∧
      ou s (evalPoly Q) (lift z 0) ≤ ou s (evalPoly Q) (lift x r) + r) := by sorry

end GeoRobustLearn
