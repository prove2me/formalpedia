-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_BKL_sum_choose_mul_sqrt_envelope_408915f
-- name    : FunctionalInequalities.KLS.BKL.sum_choose_mul_sqrt_envelope_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T14:16:36.535259+00:00
-- url     : https://prove2.me/theorems/5b7813f3-eb79-4dc3-b5cb-8297ff668749
-- title:
--   Summed Binomial Envelope Identity
-- statement:
--   This formalizes the summation identity (106) from BKL.
--
--   Let $K\ge0$ and let $m\ge3$. With $b_j=\operatorname{envelope}(K,j)$,
--
--   $$
--   \sum_{a=2}^{m-2}
--   \binom{m-1}{a-1}\sqrt{b_a b_{m-a+1}}
--   =(m-3)\sqrt{b_m}.
--   $$
--
--   The identity counts the $m-3$ terms in the indicated integer interval and is used in the scalar envelope recurrence.
-- source:
--   Source: Bizeul–Klartag–Lehec, Presenting a proof of the Kannan–Lovász–Simonovits conjecture (arXiv:2610.05474v1), Theorem 4.1, p. 18. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/BKL/CumulantEnvelope.lean#L98-L127 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.BKL.CumulantEnvelope`, declaration `FunctionalInequalities.KLS.BKL.sum_choose_mul_sqrt_envelope`; the repository is private at upload time).

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

theorem FunctionalInequalities.KLS.BKL.sum_choose_mul_sqrt_envelope_408915f {K : ℝ} (hK : 0 ≤ K) {m : ℕ} (hm : 3 ≤ m) :
    ∑ a ∈ Finset.Icc 2 (m - 2),
        ((m - 1).choose (a - 1) : ℝ) * Real.sqrt (envelope K a * envelope K (m - a + 1)) =
      ((m - 3 : ℕ) : ℝ) * Real.sqrt (envelope K m) := by sorry
