-- Prove2me | Theorems.Thm_LinearSetReconciliation327_Main_lemma_4_5
-- name    : LinearSetReconciliation327.Main.lemma_4_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:30:35.546501+00:00
-- url     : https://prove2.me/theorems/f1cec2cd-c379-4bd1-8bd5-4226e9503b9a
-- title:
--   Lemma 4.5 — Entropy from the mean
-- statement:
--   For any law of a nonnegative-integer random variable $T$ with finite mean, including infinite support and mean zero, $H(T)\le\log(e(1+\mathbb ET))$, with the entropy an extended nonnegative sum.
--
--   Differences from the source:
--   - encoding: a random variable T with distribution p → a PMF on ℕ; reason: entropy and mean depend only on the law
-- source:
--   Tianren Liu, Rui Xu, Tong Yang, Kangyang Zhou, STOC 2027 submission #327 (October 2026), Lemma 4.5, PDF p.17 (printed p.16)

import Mathlib
import Definitions.Def_LinearSetReconciliation327_Main_Basic

open scoped ENNReal
open Finset

namespace LinearSetReconciliation327.Main

/-- Lemma 4.5 (Entropy from the mean), PDF p.17 (printed p.16): any law on the nonnegative integers
with finite mean, including infinite support and mean zero. -/
theorem lemma_4_5 (T : PMF ℕ) (hmean : ∑' k : ℕ, (k : ℝ≥0∞) * T k ≠ ⊤) :
    entropy (fun k => (T k).toReal) ≤
      ENNReal.ofReal (lg (Real.exp 1 * (1 + (∑' k : ℕ, (k : ℝ≥0∞) * T k).toReal))) := by sorry

end LinearSetReconciliation327.Main
