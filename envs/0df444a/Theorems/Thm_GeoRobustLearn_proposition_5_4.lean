-- Prove2me | Theorems.Thm_GeoRobustLearn_proposition_5_4
-- name    : GeoRobustLearn.proposition_5_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T04:07:55.51988+00:00
-- url     : https://prove2.me/theorems/6094bef0-3d23-45ea-904b-f497510e16bd
-- title:
--   Proposition 5.4 — noise does not increase the defect: $\mathrm{def}_{T_sf}\le T_s\mathrm{def}_f$
-- statement:
--   Let $d\ge1$, $f$ a polynomial on $\mathbb R^d\times\mathbb R$ and $s>0$. For every $(x,a)\in\mathbb R^d\times\mathbb R$,
--
--   $$\mathrm{def}_{T_sf}(x,a)\le(T_s\mathrm{def}_f)(x,a).$$
--
--   Smoothing therefore never creates certificate defect.
--
--   Differences from the source:
--   - encoding: f : ℝ^d × ℝ → ℝ a polynomial → evalPoly Q for a real polynomial Q in the d + 1 coordinates of Space (d+1), the offset a being the last coordinate; reason: Lean representation of ℝ^d × ℝ; same instances
--   - generalization: the standing assumption σ_s < 1/2 of §3.3 (p.14) → every s > 0; reason: the proofs (§5.4–5.10, App. D) use only σ_s ≤ 1 and ρ_s ≤ 1 (paper.md decision 10); every s with σ_s < 1/2 is covered
--   - encoding: T_s(·) and expectations of the nonnegative quantities def_F, def_F², max{0, ±W} → lower Lebesgue integrals in [0, ∞] (ouLin, ∫⁻); reason: same values whenever finite; avoids the junk value 0 of a Bochner integral
-- source:
--   Lange, Marcussen, Vasilyan, Geometrically Constrained Learning I: Agnostically Learning Adversarially Robust Classifiers, manuscript (Nov. 3, 2026; sha256 8cbf3f52…), Proposition 5.4, p.23 (PDF p.23)

import Definitions.Def_GeoRobustLearn_CertDefect

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace GeoRobustLearn

open GeoLipLearn.Agnostic

/-- **Proposition 5.4** (Noise does not increase the defect), p.23.

Lange, Marcussen, Vasilyan, *Geometrically Constrained Learning I*, manuscript of November 3, 2026
(sha256 8cbf3f52…).

Let `d ≥ 1`, `F : ℝ^d × ℝ → ℝ` a polynomial and `s > 0`. For every `(x, a) ∈ ℝ^d × ℝ`,
`def_{T_s F}(x, a) ≤ (T_s def_F)(x, a)`.

**Formalization Note.** `F = evalPoly Q`; `T_s F` is the published `ou s` (a polynomial function,
since `T_s` preserves polynomials), and `T_s def_F` is `ouLin` of the nonnegative `def_F`. -/
theorem proposition_5_4 (d : ℕ) (hd : 1 ≤ d) (Q : GeoLipLearn.Agnostic.Poly (d+1))
    (s : ℝ)
    (hs : 0 < s) (z : Space (d+1)) :
    ENNReal.ofReal (certDefect (ou s (evalPoly Q)) z) ≤ ouLin s (certDefect (evalPoly Q)) z := by sorry

end GeoRobustLearn
