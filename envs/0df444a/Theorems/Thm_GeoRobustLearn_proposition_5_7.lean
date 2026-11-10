-- Prove2me | Theorems.Thm_GeoRobustLearn_proposition_5_7
-- name    : GeoRobustLearn.proposition_5_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T04:08:44.313536+00:00
-- url     : https://prove2.me/theorems/97f129d3-bf6e-4d35-ac95-c701fc545d21
-- title:
--   Proposition 5.7 — the average defect controls the negative part of the signed width
-- statement:
--   Let $d\ge1$, $f$ a polynomial on $\mathbb R^d\times\mathbb R$, $s>0$ and $r\in[0,1]$. For $x\in\mathbb R^d$ let $W(x)=(T_sf)(x,r)-(T_sf)(x,-r)$, and write $\mathcal D=\mathbb E_{(x,a)\sim N(0,I_{d+1})}[\mathrm{def}_f(x,a)^2]$. Then:
--
--   1. $$\mathbb E_{x\sim\gamma}[\max\{0,-W(x)\}]\le\frac{4r}{\sigma_s}\sqrt{\mathcal D};$$
--   2. if $K\ge0$ and $\mathbb E_{x\sim\gamma}[W(x)]\le Kr$, then $$\mathbb E_{x\sim\gamma}[\max\{0,W(x)\}]\le Kr+\frac{4r}{\sigma_s}\sqrt{\mathcal D}.$$
--
--   It converts the linear signed-width constraint into a bound on the expected danger-interval width.
--
--   Differences from the source:
--   - encoding: f : ℝ^d × ℝ → ℝ a polynomial → evalPoly Q for a real polynomial Q in the d + 1 coordinates of Space (d+1), the offset a being the last coordinate; reason: Lean representation of ℝ^d × ℝ; same instances
--   - generalization: the standing assumption σ_s < 1/2 of §3.3 (p.14) → every s > 0; reason: the proofs (§5.4–5.10, App. D) use only σ_s ≤ 1 and ρ_s ≤ 1 (paper.md decision 10); every s with σ_s < 1/2 is covered
--   - encoding: T_s(·) and expectations of the nonnegative quantities def_F, def_F², max{0, ±W} → lower Lebesgue integrals in [0, ∞] (ouLin, ∫⁻); reason: same values whenever finite; avoids the junk value 0 of a Bochner integral
--   - encoding: E_{x∼γ}[W(x)] in the hypothesis of (ii) → the Bochner integral of the polynomial W; reason: W is integrable, so this is the expectation
-- source:
--   Lange, Marcussen, Vasilyan, Geometrically Constrained Learning I: Agnostically Learning Adversarially Robust Classifiers, manuscript (Nov. 3, 2026; sha256 8cbf3f52…), Proposition 5.7, p.24 (PDF p.24)

import Definitions.Def_GeoRobustLearn_OffsetLift
import Definitions.Def_GeoRobustLearn_CertDefect

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace GeoRobustLearn

open GeoLipLearn.Agnostic

/-- **Proposition 5.7** (Small average defect controls the negative part of the signed width), p.24.

Lange, Marcussen, Vasilyan, *Geometrically Constrained Learning I*, manuscript of November 3, 2026
(sha256 8cbf3f52…).

Let `d ≥ 1`, `F` a polynomial on `ℝ^d × ℝ`, `s > 0`, `r ∈ [0, 1]`, and
`W(x) = (T_s F)(x, r) − (T_s F)(x, −r)`. Write `𝒟 = E_{(x,a)∼N(0, I_{d+1})}[def_F(x, a)²]`. Then
1. `E_{x∼γ}[max{0, −W(x)}] ≤ (4r/σ_s) √𝒟`;
2. if `K ≥ 0` and `E_{x∼γ}[W(x)] ≤ K r`, then `E_{x∼γ}[max{0, W(x)}] ≤ K r + (4r/σ_s) √𝒟`.

**Formalization Note.** `F = evalPoly Q`, `T_s F = ou s F`. The expectations of the nonnegative
quantities `max{0, ±W}` and `def_F²` are lower Lebesgue integrals in `[0, ∞]`; `E[W]` in the
hypothesis of (ii) is the Bochner integral of the polynomial `W`, which is integrable. -/
theorem proposition_5_7 (d : ℕ) (hd : 1 ≤ d) (Q : GeoLipLearn.Agnostic.Poly (d+1))
    (s : ℝ) (hs : 0 < s)
    (r : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    let W : Space d → ℝ := fun x => ou s (evalPoly Q) (lift x r) - ou s (evalPoly Q) (lift x (-r))
    let Dsq : ℝ≥0∞ := ∫⁻ w, ENNReal.ofReal (certDefect (evalPoly Q) w ^ 2) ∂gaussian (d+1)
    (∫⁻ x, ENNReal.ofReal (max 0 (-W x)) ∂gaussian d ≤
      ENNReal.ofReal (4 * r / sigma s) * Dsq ^ (1 / 2 : ℝ)) ∧
    (∀ K : ℝ, 0 ≤ K → ∫ x, W x ∂gaussian d ≤ K * r →
      ∫⁻ x, ENNReal.ofReal (max 0 (W x)) ∂gaussian d ≤
        ENNReal.ofReal (K * r) + ENNReal.ofReal (4 * r / sigma s) * Dsq ^ (1 / 2 : ℝ)) := by sorry

end GeoRobustLearn
