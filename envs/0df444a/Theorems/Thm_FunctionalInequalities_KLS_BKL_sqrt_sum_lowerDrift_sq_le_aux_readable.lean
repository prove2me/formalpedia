-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_BKL_sqrt_sum_lowerDrift_sq_le_aux_readable
-- name    : FunctionalInequalities.KLS.BKL.sqrt_sum_lowerDrift_sq_le_aux_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:14:06.817564+00:00
-- url     : https://prove2.me/theorems/6205a939-9cd4-490f-9fe8-892a2e4d1cda
-- title:
--   Pointwise Lower-Drift Square-Sum Bound
-- statement:
--   This is the Section 6 pointwise estimate with order parameter $m=k+1$.
--
--   Let $\nu$ be a compactly supported probability measure on $\mathbb{R}^n$ with invertible covariance operator that is strictly positive on nonzero vectors. Let $k\in\mathbb{N}$, let $b:\mathbb{N}\to\mathbb{R}$, and assume that for every $r$ with $2\le r<k+1$ and every $v$,
--
--   $$
--   E_{r-1}(v)\le b(r)\langle Av,v\rangle.
--   $$
--
--   Then for every $u\in\mathbb{R}^n$,
--
--   $$
--   \sqrt{\sum_{J:\operatorname{Fin}(k)\to\operatorname{Fin}(n)}
--   L(\nu)(u,\sigma e_{J_1},\ldots,\sigma e_{J_k})^2}
--   \le
--   \sum_{a\in[2,k-1]}
--   \binom{k}{a-1}
--   \sqrt{b(k+2-a)E_a(u)}.
--   $$
--
--   Here `lowerDrift`, `sigmaBasis`, and `cumulantEnergy` are the formalized quantities. The result supplies the pointwise middle-term estimate used in the cumulant-energy induction.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.KLS.BKL`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem sqrt_sum_lowerDrift_sq_le_aux (ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
--       (hc : IsCompact (ν : Measure (EuclideanSpace ℝ (Fin n))).support)
--       (hA : IsUnit (Covariance.operator (ν : Measure (EuclideanSpace ℝ (Fin n)))))
--       (hApos : ∀ v, v ≠ 0 → 0 < ⟪Covariance.operator (ν : Measure (EuclideanSpace ℝ (Fin n))) v, v⟫)
--       (k : ℕ) (b : ℕ → ℝ)
--       (h100 : ∀ r, 2 ≤ r → r < k + 1 → ∀ v : EuclideanSpace ℝ (Fin n),
--         cumulantEnergy (ν : Measure (EuclideanSpace ℝ (Fin n))) (r - 1) v ≤
--           b r * ⟪Covariance.operator (ν : Measure (EuclideanSpace ℝ (Fin n))) v, v⟫)
--       (u : EuclideanSpace ℝ (Fin n)) :
--       Real.sqrt (∑ J : Fin k → Fin n,
--           lowerDrift (ν : Measure (EuclideanSpace ℝ (Fin n)))
--             (Fin.cons u fun i => inverseSqrt (Covariance.operator (ν : Measure (EuclideanSpace ℝ (Fin n))))
--               (EuclideanSpace.basisFun (Fin n) ℝ (J i)) : Fin (k + 1) → EuclideanSpace ℝ (Fin n)) 0 ^ 2) ≤
--         ∑ a ∈ Finset.Icc 2 (k - 1), (k.choose (a - 1) : ℝ) *
--           Real.sqrt (b (k + 2 - a) * cumulantEnergy (ν : Measure (EuclideanSpace ℝ (Fin n))) a u)
--   ```
--
--   **Module navigation**
--
--   Module: [`KLS/BKL/CumulantEnergy/Basic`](https://prove2.me/theorems/4f12a1ef-12d3-46f5-b544-7dda9d084086).
--
--   Definition modules: [`Probability/Covariance/Basic`](https://prove2.me/theorems/c4e236b4-be51-468e-9de3-e2203fe87adc), [`Analysis/Operator/InverseSqrt`](https://prove2.me/theorems/2794bd57-af01-4015-a91a-cb7827d3a533).
--
--   Supporting theorems: [`sqrt_sum_sq_sum_le`](https://prove2.me/theorems/f159c409-0b24-4a71-8718-4a4409e0445e), [`sum_selected_eq`](https://prove2.me/theorems/fa7bea17-a11a-4926-a7d5-5e7c584f47ec), [`sum_sq_pairTerm_ofFn_le`](https://prove2.me/theorems/dd204f83-a393-4ef0-af4b-7c00fc22f487).
--
--   Previous: [`sum_sq_pairTerm_ofFn_le`](https://prove2.me/theorems/dd204f83-a393-4ef0-af4b-7c00fc22f487).
--
--   [Source excerpt, lines 433–447](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/BKL/CumulantEnergy/Basic.lean#L433-L447) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/BKL/CumulantEnergy/Basic.lean#L432-L527 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.BKL.CumulantEnergy.Basic`, declaration `FunctionalInequalities.KLS.BKL.sqrt_sum_lowerDrift_sq_le_aux`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_CumulantEnergy_Basic

open MeasureTheory
open FunctionalInequalities.Analysis FunctionalInequalities.Analysis.BakryEmery
open scoped RealInnerProductSpace
variable {n : ℕ}

theorem FunctionalInequalities.KLS.BKL.sqrt_sum_lowerDrift_sq_le_aux_readable (ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
    (hc : IsCompact (ν : Measure (EuclideanSpace ℝ (Fin n))).support)
    (hA : IsUnit (Covariance.operator (ν : Measure (EuclideanSpace ℝ (Fin n)))))
    (hApos : ∀ v, v ≠ 0 → 0 < ⟪Covariance.operator (ν : Measure (EuclideanSpace ℝ (Fin n))) v, v⟫)
    (k : ℕ) (b : ℕ → ℝ)
    (h100 : ∀ r, 2 ≤ r → r < k + 1 → ∀ v : EuclideanSpace ℝ (Fin n),
      cumulantEnergy (ν : Measure (EuclideanSpace ℝ (Fin n))) (r - 1) v ≤
        b r * ⟪Covariance.operator (ν : Measure (EuclideanSpace ℝ (Fin n))) v, v⟫)
    (u : EuclideanSpace ℝ (Fin n)) :
    Real.sqrt (∑ J : Fin k → Fin n,
        lowerDrift (ν : Measure (EuclideanSpace ℝ (Fin n)))
          (Fin.cons u fun i => inverseSqrt (Covariance.operator (ν : Measure (EuclideanSpace ℝ (Fin n))))
            (EuclideanSpace.basisFun (Fin n) ℝ (J i)) : Fin (k + 1) → EuclideanSpace ℝ (Fin n)) 0 ^ 2) ≤
      ∑ a ∈ Finset.Icc 2 (k - 1), (k.choose (a - 1) : ℝ) *
        Real.sqrt (b (k + 2 - a) * cumulantEnergy (ν : Measure (EuclideanSpace ℝ (Fin n))) a u) := by sorry
