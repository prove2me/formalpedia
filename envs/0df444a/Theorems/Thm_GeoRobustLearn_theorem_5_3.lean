-- Prove2me | Theorems.Thm_GeoRobustLearn_theorem_5_3
-- name    : GeoRobustLearn.theorem_5_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T04:08:38.517024+00:00
-- url     : https://prove2.me/theorems/9725be62-deb0-4f7a-afcb-95556d73aec0
-- title:
--   Theorem 5.3 — program output guarantees (i)–(iii)
-- statement:
--   Let $d\ge1$, $f$ a polynomial on $\mathbb R^d\times\mathbb R$, $s>0$, $r\in[0,1]$ and $\alpha\in(0,1]$. Suppose
--
--   $$\mathbb E_{(x,a)\sim N(0,I_{d+1})}[\mathrm{def}_f(x,a)^2]\le\alpha\,\sigma_s^2\,e^{-2r^2/\sigma_s^2}.$$
--
--   Then:
--
--   1. $\mathbb E_{x\sim\gamma}\big[T_s(\mathrm{def}_f^2)(x,0)\big]\le\alpha\,e^{-2r^2/\sigma_s^2}$;
--   2. for every $x$ with $T_s(\mathrm{def}_f^2)(x,0)\le e^{-2r^2/\sigma_s^2}$ and every $z$ with $\|z-x\|_2\le r$, $\;(T_sf)(x,-r)-r\le(T_sf)(z,0)\le(T_sf)(x,r)+r$;
--   3. with $W(x)=(T_sf)(x,r)-(T_sf)(x,-r)$: if $K\ge0$ and $\mathbb E_{x\sim\gamma}[W(x)]\le Kr$, then $\mathbb E_{x\sim\gamma}[\max\{0,W(x)\}]\le(K+4)r$.
--
--   This is the paper's main analytic result: a small average defect gives local range certificates around most points and a small expected danger interval.
--
--   Differences from the source:
--   - encoding: f : ℝ^d × ℝ → ℝ a polynomial → evalPoly Q for a real polynomial Q in the d + 1 coordinates of Space (d+1), the offset a being the last coordinate; reason: Lean representation of ℝ^d × ℝ; same instances
--   - generalization: the standing assumption σ_s < 1/2 of §3.3 (p.14) → every s > 0; reason: the proofs (§5.4–5.10, App. D) use only σ_s ≤ 1 and ρ_s ≤ 1 (paper.md decision 10); every s with σ_s < 1/2 is covered
--   - encoding: T_s(·) and expectations of the nonnegative quantities def_F, def_F², max{0, ±W} → lower Lebesgue integrals in [0, ∞] (ouLin, ∫⁻); reason: same values whenever finite; avoids the junk value 0 of a Bochner integral
--   - encoding: E_{x∼γ}[W(x)] in the hypothesis of (iii) → the Bochner integral of the polynomial W; reason: W is integrable, so this is the expectation
-- source:
--   Lange, Marcussen, Vasilyan, Geometrically Constrained Learning I: Agnostically Learning Adversarially Robust Classifiers, manuscript (Nov. 3, 2026; sha256 8cbf3f52…), Theorem 5.3, pp.22–23 (PDF pp.22–23)

import Definitions.Def_GeoRobustLearn_OffsetLift
import Definitions.Def_GeoRobustLearn_CertDefect

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace GeoRobustLearn

open GeoLipLearn.Agnostic

/-- **Theorem 5.3** (Program output guarantees), pp.22–23.

Lange, Marcussen, Vasilyan, *Geometrically Constrained Learning I*, manuscript of November 3, 2026
(sha256 8cbf3f52…).

Let `d ≥ 1`, `F` a polynomial on `ℝ^d × ℝ`, `s > 0`, `r ∈ [0, 1]` and `α ∈ (0, 1]`. Suppose
`E_{(x,a)∼N(0, I_{d+1})}[def_F(x, a)²] ≤ α σ_s² e^{−2r²/σ_s²}`. Then
1. `E_{x∼γ}[T_s(def_F²)(x, 0)] ≤ α e^{−2r²/σ_s²}`;
2. for every `x` with `T_s(def_F²)(x, 0) ≤ e^{−2r²/σ_s²}` and every `z` with `‖z − x‖₂ ≤ r`,
   `(T_s F)(x, −r) − r ≤ (T_s F)(z, 0) ≤ (T_s F)(x, r) + r`;
3. with `W(x) = (T_s F)(x, r) − (T_s F)(x, −r)`: if `K ≥ 0` and `E_{x∼γ}[W(x)] ≤ K r`, then
   `E_{x∼γ}[max{0, W(x)}] ≤ (K + 4) r`.

**Formalization Note.** `F = evalPoly Q`, `T_s F = ou s F`; `T_s(def_F²)` is `ouLin` of the
nonnegative `def_F²`; expectations of nonnegative quantities are lower Lebesgue integrals, and
`E[W]` is the Bochner integral of the polynomial `W`. `σ_s = sigma s`. -/
theorem theorem_5_3 (d : ℕ) (hd : 1 ≤ d) (Q : GeoLipLearn.Agnostic.Poly (d+1))
    (s : ℝ) (hs : 0 < s)
    (r α : ℝ) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hdef : ∫⁻ w, ENNReal.ofReal (certDefect (evalPoly Q) w ^ 2) ∂gaussian (d+1) ≤
      ENNReal.ofReal (α * sigma s ^ 2 * Real.exp (-2 * r ^ 2 / sigma s ^ 2))) :
    (∫⁻ x, ouLin s (fun w => certDefect (evalPoly Q) w ^ 2) (lift x 0) ∂gaussian d ≤
      ENNReal.ofReal (α * Real.exp (-2 * r ^ 2 / sigma s ^ 2))) ∧
    (∀ x : Space d,
      ouLin s (fun w => certDefect (evalPoly Q) w ^ 2) (lift x 0) ≤
        ENNReal.ofReal (Real.exp (-2 * r ^ 2 / sigma s ^ 2)) →
      ∀ z : Space d, ‖z - x‖ ≤ r →
        ou s (evalPoly Q) (lift x (-r)) - r ≤ ou s (evalPoly Q) (lift z 0) ∧
        ou s (evalPoly Q) (lift z 0) ≤ ou s (evalPoly Q) (lift x r) + r) ∧
    (∀ K : ℝ, 0 ≤ K →
      ∫ x, (ou s (evalPoly Q) (lift x r) - ou s (evalPoly Q) (lift x (-r))) ∂gaussian d ≤ K * r →
      ∫⁻ x, ENNReal.ofReal (max 0
          (ou s (evalPoly Q) (lift x r) - ou s (evalPoly Q) (lift x (-r)))) ∂gaussian d ≤
        ENNReal.ofReal ((K + 4) * r)) := by sorry

end GeoRobustLearn
