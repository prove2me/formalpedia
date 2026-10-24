-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_BKL_choose_mul_sqrt_envelope_408915f
-- name    : FunctionalInequalities.KLS.BKL.choose_mul_sqrt_envelope_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T14:16:35.766313+00:00
-- url     : https://prove2.me/theorems/738737d9-7672-42e6-bb53-449f06b836b9
-- title:
--   Binomial Envelope Product Identity
-- statement:
--   This formalizes the binomial identity (105) from BKL.
--
--   Let $K\ge0$ and let integers $m,a$ satisfy $1\le a\le m$. For $b_j=\operatorname{envelope}(K,j)=K^{j-1}((j-1)!)^2$, one has
--
--   $$
--   \binom{m-1}{a-1}\sqrt{b_a b_{m-a+1}}
--   =\sqrt{b_m}.
--   $$
--
--   The identity is purely arithmetic and is used to normalize the terms in the cumulant-envelope induction.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/BKL/CumulantEnvelope.lean#L26-L86 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.BKL.CumulantEnvelope`, declaration `FunctionalInequalities.KLS.BKL.choose_mul_sqrt_envelope`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_BKL_CumulantEnvelope
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Nat.Choose.Basic

noncomputable section
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.KLS
end FunctionalInequalities.KLS
open FunctionalInequalities FunctionalInequalities.KLS
section
namespace FunctionalInequalities.KLS.BKL
end FunctionalInequalities.KLS.BKL
open FunctionalInequalities FunctionalInequalities.KLS FunctionalInequalities.KLS.BKL

theorem FunctionalInequalities.KLS.BKL.choose_mul_sqrt_envelope_408915f {K : ℝ} (hK : 0 ≤ K) {m a : ℕ} (ha : 1 ≤ a) (ham : a ≤ m) :
    ((m - 1).choose (a - 1) : ℝ) * Real.sqrt (envelope K a * envelope K (m - a + 1)) =
      Real.sqrt (envelope K m) := by sorry
