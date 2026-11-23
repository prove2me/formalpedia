-- Prove2me | Theorems.Thm_ITPIRPreproc_MatchVec_padded_scheme_adapter
-- name    : ITPIRPreproc.MatchVec.padded_scheme_adapter
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-23T03:24:16.46532+00:00
-- url     : https://prove2.me/theorems/3303e41e-accf-4ec2-a1b4-9e20820546e6
-- title:
--   Uniform zero-padding adapter for preprocessing PIR
-- statement:
--   There is one uniform word-RAM construction turning any well-formed scheme \(S\) into a well-formed scheme \(T\) at arbitrary database lengths. At input length \(n\), \(T\) runs \(S\) at length \(N(n)=4^{h(n)}\) on \(D\Vert 0^{N(n)-n}\), including zero bits virtually in the offline answer. Real indices are embedded unchanged, and answers for indices in the padded region are computed within the simulation so the full source scheme remains honest. Queries, outputs, transitions and hence the simulator view and failure event are coupled exactly. Consequently perfect privacy and the identical \(T2^{-\lambda}\) correctness bound transfer, and every source cost bound transfers with at most a fixed RAM-word simulation factor \(A\), plus \(A N(n)\) preprocessing work and \(A n^{1/4}\) header/work/space allowance. Online and offline communication are unchanged.
-- source:
--   Dujmovic–Lai–Wichs, STOC 2027 submission #572, proof of Theorem 6.1, PDF p.26 (choose a power of four at most 64n and pad with zero, running the programs as if the length were the padded length); §3 pp.8–10 for the experiment and Appendix A pp.38–39 for uniform RAM simulation. The additive wrapper allowance is part of the formal adapter’s explicit honest simulation cost.

import Definitions.Def_ITPIRPreproc_MatchVec_PowerFourPadding

open scoped ENNReal
open Filter Topology

open ITPIRPreproc.MatchVec

theorem ITPIRPreproc.MatchVec.padded_scheme_adapter
    (S : Scheme) (hS : S.WellFormed) :
    ∃ A : ℝ, 1 ≤ A ∧ ∃ T : Scheme, T.WellFormed ∧
      ∀ (n lam : ℕ) (B : Budget), 1 ≤ n →
        PerfectlyPrivate S (padLength n) lam →
        Correct S (padLength n) lam (fun T => (T : ℝ≥0∞) * (2⁻¹ : ℝ≥0∞) ^ lam) →
        MeetsBudget S (padLength n) lam B →
        PerfectlyPrivate T n lam ∧
        Correct T n lam (fun T => (T : ℝ≥0∞) * (2⁻¹ : ℝ≥0∞) ^ lam) ∧
        MeetsBudget T n lam (adapterBudget A n B) := by sorry
