-- Prove2me | Theorems.Thm_LL_SquareWave1124_leaf_smoothed_square_wave_series
-- name    : LL_SquareWave1124.leaf_smoothed_square_wave_series
-- status  : Open
-- author  : @sthubbar
-- created : 2026-11-27T05:51:03.454207+00:00
-- url     : https://prove2.me/theorems/e746e637-dccd-4052-9159-d7cb5a00bbb5
-- title:
--   Fourier series of the smoothed square wave with coefficients $\le C\,W_\Delta(h)$
-- statement:
--   There is $C>0$ such that for every $0<\Delta\le1/4$ there are $c:\mathbb Z\to\mathbb C$ with $|c_h|\le C\,W_\Delta(h)$ for all $h$, and for every real $x$ the family $h\mapsto c_h\,e(hx/2)$ has a sum $T$ over $\mathbb Z$, with $T=(-1)^{\lfloor x\rfloor}$ whenever $\Delta\le\{x\}\le1-\Delta$.
-- source:
--   Brüdern and Perelli 1998, Section 7, page 370, display (40).

import Mathlib
import Definitions.Def_LL_SquareWave1124_sqW
import Definitions.Def_LL_SquareWave1124_eC

namespace LL_SquareWave1124
theorem leaf_smoothed_square_wave_series :
    ∃ C : ℝ, 0 < C ∧ ∀ Δ : ℝ, 0 < Δ → Δ ≤ 1 / 4 →
      ∃ c : ℤ → ℂ, (∀ h : ℤ, ‖c h‖ ≤ C * sqW Δ h) ∧
        ∀ x : ℝ, ∃ T : ℂ,
          (Δ ≤ Int.fract x → Int.fract x ≤ 1 - Δ → T = (-1 : ℂ) ^ ⌊x⌋) ∧
          HasSum (fun h : ℤ => c h * eC ((h : ℝ) / 2 * x)) T := by sorry
end LL_SquareWave1124
