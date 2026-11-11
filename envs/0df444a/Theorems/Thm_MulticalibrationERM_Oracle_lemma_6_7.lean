-- Prove2me | Theorems.Thm_MulticalibrationERM_Oracle_lemma_6_7
-- name    : MulticalibrationERM.Oracle.lemma_6_7
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T16:50:33.053712+00:00
-- url     : https://prove2.me/theorems/568cc924-1ad4-4177-9984-ddbd102683e8
-- title:
--   Lemma 6.7 — the minimax forecast on consecutive grid values
-- statement:
--   There is an absolute constant $C$ such that for every $K\ge1$, all grid values $v_{lo}=lo/K\le v_{hi}=hi/K$ and every $a\in[-1,1]^{\Lambda'}$, $\Lambda'=\Lambda\cap[v_{lo},v_{hi}]$, the restricted minimax forecast $P=\mathrm{Minimax}_{\Lambda'}(a)$ is a distribution on $\Lambda'$ with adjacent support, computed with at most $C\,m$ elementary operations, and with $\mu=\sum_vP(v)\,v$,
--   $$(\mu-y)\sum_{v\in\Lambda'}P(v)\,a_v\le0\qquad\text{for every }y\in[v_{lo},v_{hi}].$$
--
--   Differences from the source:
--   - encoding: computable in O(m) time → the operation count minimaxOps of the stated procedure (unit-cost model) is at most C·m for an absolute C; reason: a running time needs a cost model
--   - encoding: a ∈ [−1,1]^{Λ'} and P ∈ Δ(Λ') → a and P are vectors on the whole grid; a is constrained only on Λ', P vanishes off Λ', and the sum runs over Λ'; reason: values off Λ' are never read
-- source:
--   Okoroafor, The Sample Complexity of Multicalibration with an ERM Oracle, supplied 61-page preprint (PDF SHA256 654c7a8127547d76c5a4b6db236ce672c2c09a70d21d56a3981583e1805d0f8d; exact arXiv revision unresolved, not arXiv:2610.14363v1), p. 35, Lemma 6.7

import Mathlib
import Definitions.Def_MulticalibrationERM_Oracle_Setting
import Definitions.Def_MulticalibrationERM_Oracle_Forecast

namespace MulticalibrationERM.Oracle

/-- Lemma 6.7 (p. 35): for `Λ' = Λ ∩ [v_lo, v_hi]` with grid values `v_lo = lo/K ≤ v_hi = hi/K`
and `a ∈ [−1, 1]^{Λ'}`, the restricted minimax forecast `P = Minimax_{Λ'}(a)` is a distribution
supported in `Λ'` with adjacent support, computed with `O(m)` operations, and with mean `µ`
satisfies `(µ − y) ∑_{v ∈ Λ'} P(v) a_v ≤ 0` for every `y ∈ [v_lo, v_hi]`. -/
theorem lemma_6_7 :
    ∃ C : ℝ, 0 < C ∧
    ∀ (K : ℕ), 1 ≤ K → ∀ (lo hi : ℕ), lo ≤ hi → hi ≤ K →
    ∀ a : Fin (K + 1) → ℝ, (∀ v : Fin (K + 1), lo ≤ (v : ℕ) → (v : ℕ) ≤ hi →
        a v ∈ Set.Icc (-1 : ℝ) 1) →
      IsDist (minimax K lo hi a) ∧
      (∀ v : Fin (K + 1), minimax K lo hi a v ≠ 0 → lo ≤ (v : ℕ) ∧ (v : ℕ) ≤ hi) ∧
      AdjSupport (minimax K lo hi a) ∧
      (minimaxOps K lo hi a : ℝ) ≤ C * (K + 1) ∧
      ∀ y ∈ Set.Icc ((lo : ℝ) / K) ((hi : ℝ) / K),
        (gridMean (minimax K lo hi a) - y) *
          ∑ v ∈ Finset.univ.filter (fun v : Fin (K + 1) => lo ≤ (v : ℕ) ∧ (v : ℕ) ≤ hi),
            minimax K lo hi a v * a v ≤ 0 := by sorry

end MulticalibrationERM.Oracle
