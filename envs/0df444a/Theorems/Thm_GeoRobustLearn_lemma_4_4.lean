-- Prove2me | Theorems.Thm_GeoRobustLearn_lemma_4_4
-- name    : GeoRobustLearn.lemma_4_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T04:08:31.627042+00:00
-- url     : https://prove2.me/theorems/6daf4853-d55d-41eb-bc9e-5eabb87f22c9
-- title:
--   Lemma 4.4 — the truncated witness $P^\star=T_sQ^\star$ has error $CK\sqrt s$ and signed width $CKr$
-- statement:
--   There are constants $C>0$ and $c_s\in(0,1]$ such that the following holds. Let $K\ge1$, $f\in\mathcal C_K$, $s\in(0,1]$, $0<r\le1/K$, $\sigma_s=\sqrt{1-e^{-2s}}$ and $0<\beta\le Kr\sigma_s$. Set $Q^\star=(T_sB_f)^{\le k}$ and $P^\star=T_sQ^\star$ with $k\ge\lceil\frac1s\log\frac4{s\beta}\rceil$. Then
--
--   1. $\mathbb E_{x\sim\gamma}|P^\star(x,0)-f(x)|\le CK\sqrt s$;
--   2. $m_{P^\star}(r)-m_{P^\star}(-r)\le CKr$, where $m_{P^\star}(a)=\mathbb E_{x\sim\gamma}P^\star(x,a)$;
--   3. if $s=c_s\varepsilon^2/K^2$ for some $\varepsilon>0$, then $\mathbb E_{x\sim\gamma}|P^\star(x,0)-f(x)|\le\varepsilon$.
--
--   So the convex program has a feasible point whose loss is within $\varepsilon$ of the error of any $f\in\mathcal C_K$.
--
--   Differences from the source:
--   - encoding: ℝ^{d+1} ∋ (x, a), T_s, F^{≤k} → Space (d+1) with the offset as last coordinate; the published ou s and truncation k; reason: Lean representation; same objects
--   - encoding: E_{x∼γ}|·(x, 0) − f(x)| → lower Lebesgue integral of ofReal |·|, with no measurability assumed of f; reason: for f ∈ C_K, f agrees with a Borel function off a Borel γ-null set, so the lower integral is the integral
--   - encoding: C (one constant for both bounds) → ∃ C > 0 before all data; reason: the meaning of the constant
--   - reading: "In particular, taking s = c_s ε²/K² gives prediction error ε" → ∃ c_s ∈ (0, 1] before all data such that s = c_s ε²/K² implies error ≤ ε; reason: c_s is the sufficiently small universal constant of §4.3 (0 < c_s ≤ 1)
-- source:
--   Lange, Marcussen, Vasilyan, Geometrically Constrained Learning I: Agnostically Learning Adversarially Robust Classifiers, manuscript (Nov. 3, 2026; sha256 8cbf3f52…), Lemma 4.4, p.20 (PDF p.20)

import Definitions.Def_GeoLipLearn_Agnostic_Hermite
import Definitions.Def_GeoRobustLearn_BoundaryVolume
import Definitions.Def_GeoRobustLearn_OffsetLift

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace GeoRobustLearn

open GeoLipLearn.Agnostic

/-- **Lemma 4.4** (Error and expected signed width bounds for the truncated witness), p.20.

Lange, Marcussen, Vasilyan, *Geometrically Constrained Learning I*, manuscript of November 3, 2026
(sha256 8cbf3f52…).

There are constants `C > 0` and `c_s ∈ (0, 1]` such that: for `K ≥ 1`, `f ∈ C_K`, `s ∈ (0, 1]`,
`0 < r ≤ 1/K`, `0 < β ≤ K r σ_s`, `Q⋆ = (T_s B_f)^{≤k}`, `P⋆ = T_s Q⋆` and
`k ≥ ⌈(1/s) log(4/(sβ))⌉`:
1. `E_{x∼γ}|P⋆(x, 0) − f(x)| ≤ C K √s`;
2. `m_{P⋆}(r) − m_{P⋆}(−r) ≤ C K r`;
3. ("in particular") if `s = c_s ε²/K²` for some `ε > 0`, then `E_{x∼γ}|P⋆(x, 0) − f(x)| ≤ ε`.

**Formalization Note.** `σ_s` is the published `sigma s`, `T_s` the published `ou s`, `(·)^{≤k}` the
published `truncation k`, all on `Space (d+1)`. `m_{P⋆}` is `offsetMean`. Both `C` and `c_s` are
chosen before all data. The expectation is a lower Lebesgue integral (see `lemma_4_1`). -/
theorem lemma_4_4 :
    ∃ C cs : ℝ, 0 < C ∧ 0 < cs ∧ cs ≤ 1 ∧
      ∀ (d : ℕ) (K s r β : ℝ) (k : ℕ) (f : Space d → ℝ),
        1 ≤ K → InCK K f → 0 < s → s ≤ 1 → 0 < r → r ≤ 1 / K →
        0 < β → β ≤ K * r * sigma s →
        ⌈(1 / s) * Real.log (4 / (s * β))⌉ ≤ (k : ℤ) →
        let Pstar : Space (d+1) → ℝ := ou s (truncation k (ou s (offsetLift f)))
        ∫⁻ x, ENNReal.ofReal |Pstar (lift x 0) - f x| ∂gaussian d ≤
          ENNReal.ofReal (C * K * Real.sqrt s) ∧
        offsetMean Pstar r - offsetMean Pstar (-r) ≤ C * K * r ∧
        (∀ ε : ℝ, 0 < ε → s = cs * ε ^ 2 / K ^ 2 →
          ∫⁻ x, ENNReal.ofReal |Pstar (lift x 0) - f x| ∂gaussian d ≤ ENNReal.ofReal ε) := by sorry

end GeoRobustLearn
