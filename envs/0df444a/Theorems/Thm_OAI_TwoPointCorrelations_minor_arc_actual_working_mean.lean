-- Prove2me | Theorems.Thm_OAI_TwoPointCorrelations_minor_arc_actual_working_mean
-- name    : OAI.TwoPointCorrelations.minor_arc_actual_working_mean
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T01:13:04.104999+00:00
-- url     : https://prove2.me/theorems/4c24aa52-08be-4093-a97f-ce8352263d00
-- title:
--   Minor-arc bound for the short exponential integral of typical numbers at the working parameters
-- statement:
--   There are $C>0$ and $W_0$ such that for all sufficiently large $L$: for every natural $H>0$ with $\log H\ge1$ and $\log\log H\ge1$, and every $M\ge0$, put $W$ = `majorArcParameter L H M` $=\min((\log H)^5,L^{1/125},e^{M/3})$, $h$ = `majorArcWorkingLength H W`, $P=W^{500000}$ and $Q=h/W^3$. If $W\ge W_0$, then for all naturals $Y\ge h$ and $J\ge1$, every multiplicative $F$ bounded by $1$ on positive integers, every $r\in\mathbb Z$ and natural $q$ with $W\le q\le h/W$, and every real $\alpha$ with $\gcd(q,r)=1$ (as integers) and $|\alpha-r/q|\le1/q^2$,
--
--   $$\int_0^Y\Big|\sum_{y<n\le y+h}G(n)e(n\alpha)\Big|dy\le C\,Y\,h\Big(e^{-M/20}+\frac{\log\log H}{\log H}+L^{-1/700}\Big),$$
--
--   where $G$ = `mrtTypicalCoefficient (Icc 1 J) (j ↦ mrtPrimeBand (mrtBandLower P Q j) (mrtBandUpper Q j)) F` and the left side is `shortExponentialIntegral G Y h α`.
-- source:
--   OpenAI, Ordinary two-point correlations of multiplicative functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/main/preprints/Ordinary-two-point-correlations-of-multiplicative-functions-September-24-2026/final.pdf; Lean: lean/OAI/NumberTheory/TwoPoint, Apache License 2.0); Lean declaration `OAI.TwoPointCorrelations.minor_arc_actual_working_mean`

import Mathlib
import Definitions.Def_OAIChowlaTwoPointDefs

namespace OAI.TwoPointCorrelations

open Filter
open Finset

theorem minor_arc_actual_working_mean :
    ∃ C : ℝ, 0 < C ∧ ∃ W₀ : ℝ, ∀ᶠ L : ℝ in atTop,
    ∀ H : ℕ, 0 < H → 1 ≤ Real.log (H:ℝ) → 1 ≤ Real.log (Real.log (H:ℝ)) →
    ∀ M : ℝ, 0 ≤ M →
      let W := majorArcParameter L H M
      let h := majorArcWorkingLength H W
      let P := W^(500000:ℕ)
      let Q := (h:ℝ)/W^3
      W₀ ≤ W → ∀ Y J : ℕ, h ≤ Y → 1 ≤ J →
    ∀ F : ℕ → ℂ, Multiplicative F → OneBounded F →
    ∀ r : ℤ, ∀ q : ℕ, W ≤ (q:ℝ) → (q:ℝ) ≤ (h:ℝ)/W →
    ∀ α : ℝ, IsCoprime (q:ℤ) r → |α-(r:ℝ)/q| ≤ 1/(q:ℝ)^2 →
      shortExponentialIntegral (mrtTypicalCoefficient (Icc 1 J)
        (fun j => mrtPrimeBand (mrtBandLower P Q j) (mrtBandUpper Q j)) F) Y h α ≤
      C*(Y:ℝ)*h*(Real.exp (-M/20)+Real.log (Real.log H)/Real.log H+L^(-1/700:ℝ)) := by
  sorry

end OAI.TwoPointCorrelations
