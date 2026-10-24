-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_BKL_absorption_le_envelope_408915f
-- name    : FunctionalInequalities.KLS.BKL.absorption_le_envelope_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T14:16:34.157541+00:00
-- url     : https://prove2.me/theorems/29a87f31-df25-491b-a335-6b3c26016438
-- title:
--   Scalar Absorption by the Cumulant Envelope
-- statement:
--   This formalizes the scalar absorption estimate after BKL (106), p. 27.
--
--   Let $C,K\in\mathbb{R}$ satisfy $C\ge0$, $K\ge9C$, and $K\ge64$. For an integer $m\ge3$, let
--
--   $$
--   b_j=\operatorname{envelope}(K,j)=K^{j-1}((j-1)!)^2.
--   $$
--
--   Then
--
--   $$
--   2Cm^2b_{m-1}+4(m-3)\sqrt{b_{m-1}b_m}\le b_m.
--   $$
--
--   This is an arithmetic estimate only; it does not assert a cumulant bound or complete the induction by itself.
-- source:
--   Source: Bizeul–Klartag–Lehec, Presenting a proof of the Kannan–Lovász–Simonovits conjecture (arXiv:2610.05474v1), Theorem 4.1, p. 18. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/BKL/CumulantEnvelope.lean#L129-L242 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.BKL.CumulantEnvelope`, declaration `FunctionalInequalities.KLS.BKL.absorption_le_envelope`; the repository is private at upload time).

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

theorem FunctionalInequalities.KLS.BKL.absorption_le_envelope_408915f {K C : ℝ} (hC : 0 ≤ C) (hK9 : 9 * C ≤ K) (hK64 : 64 ≤ K)
    {m : ℕ} (hm : 3 ≤ m) :
    2 * C * (m : ℝ) ^ 2 * envelope K (m - 1) +
        4 * ((m - 3 : ℕ) : ℝ) * Real.sqrt (envelope K (m - 1) * envelope K m) ≤
      envelope K m := by sorry
