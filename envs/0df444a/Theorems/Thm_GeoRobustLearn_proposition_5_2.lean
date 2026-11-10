-- Prove2me | Theorems.Thm_GeoRobustLearn_proposition_5_2
-- name    : GeoRobustLearn.proposition_5_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T04:08:41.203801+00:00
-- url     : https://prove2.me/theorems/15b305f5-9abc-4dcf-85dc-24a4ad819b53
-- title:
--   Proposition 5.2 — defect $\le\beta$ on the segment gives $f(x,-r)-\beta r\le f(z,0)\le f(x,r)+\beta r$
-- statement:
--   Let $d\ge1$ and let $f:\mathbb R^d\times\mathbb R\to\mathbb R$ be a polynomial. Fix $x,z\in\mathbb R^d$, let $r\ge\|z-x\|_2$ and $\beta\ge0$. Suppose $\mathrm{def}_f(y,a)\le\beta$ for every $y$ on the line segment joining $x$ to $z$ and every $a\in[-r,r]$. Then
--
--   $$f(x,-r)-\beta r\le f(z,0)\le f(x,r)+\beta r.$$
--
--   The offset coordinate acts as a budget that pays for spatial displacement; this is the comparison inequality behind the local range certificates.
--
--   Differences from the source:
--   - encoding: f : ℝ^d × ℝ → ℝ a polynomial → evalPoly Q for a real polynomial Q in the d + 1 coordinates of Space (d+1), the offset a being the last coordinate; reason: Lean representation of ℝ^d × ℝ; same instances
-- source:
--   Lange, Marcussen, Vasilyan, Geometrically Constrained Learning I: Agnostically Learning Adversarially Robust Classifiers, manuscript (Nov. 3, 2026; sha256 8cbf3f52…), Proposition 5.2, p.22 (PDF p.22); standing assumptions §5.1, p.22

import Definitions.Def_GeoRobustLearn_OffsetLift
import Definitions.Def_GeoRobustLearn_CertDefect

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace GeoRobustLearn

open GeoLipLearn.Agnostic

/-- **Proposition 5.2**, p.22.

Lange, Marcussen, Vasilyan, *Geometrically Constrained Learning I*, manuscript of November 3, 2026
(sha256 8cbf3f52…).

Let `d ≥ 1` and let `F : ℝ^d × ℝ → ℝ` be a polynomial. Fix `x, z ∈ ℝ^d`, `r ≥ ‖z − x‖₂` and `β ≥ 0`.
If `def_F(y, a) ≤ β` for every `y` on the segment `[x, z]` and every `a ∈ [−r, r]`, then
`F(x, −r) − βr ≤ F(z, 0) ≤ F(x, r) + βr`.

**Formalization Note.** `F` is `evalPoly Q` for a real polynomial `Q` in the `d + 1` coordinates of
`Space (d+1)` (§5.1: "f : ℝ^d × ℝ → ℝ is a polynomial"; named `Q` here, as the paper applies §5 to
the auxiliary polynomial). `def_F` is `certDefect`. -/
theorem proposition_5_2 (d : ℕ) (hd : 1 ≤ d) (Q : GeoLipLearn.Agnostic.Poly (d+1))
    (x z : Space d) (r β : ℝ)
    (hr : ‖z - x‖ ≤ r) (hβ : 0 ≤ β)
    (hdef : ∀ y ∈ segment ℝ x z, ∀ a ∈ Set.Icc (-r) r,
      certDefect (evalPoly Q) (lift y a) ≤ β) :
    evalPoly Q (lift x (-r)) - β * r ≤ evalPoly Q (lift z 0) ∧
    evalPoly Q (lift z 0) ≤ evalPoly Q (lift x r) + β * r := by sorry

end GeoRobustLearn
