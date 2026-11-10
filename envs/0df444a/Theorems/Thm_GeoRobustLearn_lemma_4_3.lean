-- Prove2me | Theorems.Thm_GeoRobustLearn_lemma_4_3
-- name    : GeoRobustLearn.lemma_4_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T04:08:29.280681+00:00
-- url     : https://prove2.me/theorems/a610f5c2-4727-4c9e-8eab-be83b4248b64
-- title:
--   Lemma 4.3 — the truncation $Q^\star=(T_sB_f)^{\le k}$ has $\|Q^\star\|_2\le1$ and squared defect $\le\beta/2$
-- statement:
--   Let $f\in\mathcal C_K$, $s\in(0,1]$, $\beta\in(0,1]$, $V=T_sB_f$ and $Q^\star=V^{\le k}$, the degree-$\le k$ Hermite truncation. If
--
--   $$k\ge\Big\lceil\frac1s\log\frac{4}{s\beta}\Big\rceil,$$
--
--   then $\|Q^\star\|_{L^2(\gamma_{d+1})}\le1$ and
--
--   $$\mathbb E_{(x,a)\sim\gamma_{d+1}}\Big[\big(\|\nabla_xQ^\star(x,a)\|_2-\partial_aQ^\star(x,a)\big)_+^2\Big]\le\frac\beta2.$$
--
--   This makes the truncated witness feasible for the norm and squared-defect constraints of the convex program.
--
--   Differences from the source:
--   - encoding: ℝ^{d+1} ∋ (x, a), T_s, F^{≤k} → Space (d+1) with the offset as last coordinate; the published ou s and truncation k; reason: Lean representation; same objects
--   - encoding: ‖Q⋆‖₂ and (u)²₊ → normG 2 (the L²(γ_{d+1}) norm) and certDefect²; reason: same quantities
-- source:
--   Lange, Marcussen, Vasilyan, Geometrically Constrained Learning I: Agnostically Learning Adversarially Robust Classifiers, manuscript (Nov. 3, 2026; sha256 8cbf3f52…), Lemma 4.3, p.19 (PDF p.19)

import Definitions.Def_GeoLipLearn_Agnostic_Hermite
import Definitions.Def_GeoRobustLearn_BoundaryVolume
import Definitions.Def_GeoRobustLearn_OffsetLift
import Definitions.Def_GeoRobustLearn_CertDefect

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace GeoRobustLearn

open GeoLipLearn.Agnostic

/-- **Lemma 4.3** (Truncation with small squared defect), p.19.

Lange, Marcussen, Vasilyan, *Geometrically Constrained Learning I*, manuscript of November 3, 2026
(sha256 8cbf3f52…).

Let `f ∈ C_K`, `s ∈ (0, 1]`, `β ∈ (0, 1]`, `V = T_s B_f` and `Q⋆ = V^{≤k}`. If
`k ≥ ⌈(1/s) log(4/(sβ))⌉`, then `‖Q⋆‖₂ ≤ 1` and
`E_{(x,a)∼γ_{d+1}}[(‖∇_x Q⋆(x, a)‖₂ − ∂_a Q⋆(x, a))²_+] ≤ β/2`.

**Formalization Note.** `Q⋆` is the published `truncation k` (the degree-`≤ k` Hermite truncation
`F^{≤k}` of §3.2) of `ou s (offsetLift f)` on `Space (d+1)`; it is a polynomial function, so its
derivatives are genuine. `‖·‖₂` is the published `normG 2` (the `L²(γ_{d+1})` norm), and
`(u)²_+ = (certDefect)²`. The ceiling is the integer ceiling of the real number, as printed. -/
theorem lemma_4_3 (d : ℕ) (K s β : ℝ) (k : ℕ) (f : Space d → ℝ)
    (hf : InCK K f) (hs0 : 0 < s) (hs1 : s ≤ 1) (hβ0 : 0 < β) (hβ1 : β ≤ 1)
    (hk : ⌈(1 / s) * Real.log (4 / (s * β))⌉ ≤ (k : ℤ)) :
    let Qstar : Space (d+1) → ℝ := truncation k (ou s (offsetLift f))
    normG 2 Qstar ≤ 1 ∧
    ∫⁻ z, ENNReal.ofReal (certDefect Qstar z ^ 2) ∂gaussian (d+1) ≤
      ENNReal.ofReal (β / 2) := by sorry

end GeoRobustLearn
