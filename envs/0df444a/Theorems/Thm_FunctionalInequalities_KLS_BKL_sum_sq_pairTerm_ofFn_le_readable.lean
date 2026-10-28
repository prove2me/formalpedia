-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_BKL_sum_sq_pairTerm_ofFn_le_readable
-- name    : FunctionalInequalities.KLS.BKL.sum_sq_pairTerm_ofFn_le_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:14:10.466796+00:00
-- url     : https://prove2.me/theorems/dd204f83-a393-4ef0-af4b-7c00fc22f487
-- title:
--   Row Contraction Bound for Pair Terms
-- statement:
--   This formalizes the row-contraction estimate corresponding to BKL (101)–(102).
--
--   Let $\nu$ be a compactly supported probability measure on $\mathbb{R}^n$ whose covariance operator $A$ is invertible and strictly positive in every nonzero direction. Let $c,c_2\in\mathbb{N}$, let $\beta\in\mathbb{R}$, and assume that for every $v\in\mathbb{R}^n$,
--
--   $$
--   E_{c_2}(v)\le \beta\langle Av,v\rangle,
--   $$
--
--   where $E_j$ is the formalized `cumulantEnergy`. Then, for every $u\in\mathbb{R}^n$,
--
--   $$
--   \sum_{J_1:\operatorname{Fin}(c)\to\operatorname{Fin}(n)}
--   \sum_{J_2:\operatorname{Fin}(c_2)\to\operatorname{Fin}(n)}
--   \operatorname{pairTerm}(\nu,u;J_1,J_2)
--   \le \beta E_{c+1}(u).
--   $$
--
--   The lists in the pair term use the covariance-normalized basis `sigmaBasis`. This is the one-mask contraction estimate used in the lower-drift bound.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.KLS.BKL`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem sum_sq_pairTerm_ofFn_le (ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
--       (hc : IsCompact (ν : Measure (EuclideanSpace ℝ (Fin n))).support)
--       (hA : IsUnit (Covariance.operator (ν : Measure (EuclideanSpace ℝ (Fin n)))))
--       (hApos : ∀ v, v ≠ 0 → 0 < ⟪Covariance.operator (ν : Measure (EuclideanSpace ℝ (Fin n))) v, v⟫)
--       {c c₂ : ℕ} (β : ℝ)
--       (h100 : ∀ v : EuclideanSpace ℝ (Fin n),
--         cumulantEnergy (ν : Measure (EuclideanSpace ℝ (Fin n))) c₂ v ≤
--           β * ⟪Covariance.operator (ν : Measure (EuclideanSpace ℝ (Fin n))) v, v⟫)
--       (u : EuclideanSpace ℝ (Fin n)) :
--       ∑ J₁ : Fin c → Fin n, ∑ J₂ : Fin c₂ → Fin n,
--         pairTerm (ν : Measure (EuclideanSpace ℝ (Fin n))) u
--           (List.ofFn fun i => sigmaBasis (ν : Measure (EuclideanSpace ℝ (Fin n))) (J₁ i))
--           (List.ofFn fun i => sigmaBasis (ν : Measure (EuclideanSpace ℝ (Fin n))) (J₂ i)) ≤
--         β * cumulantEnergy (ν : Measure (EuclideanSpace ℝ (Fin n))) (c + 1) u
--   ```
--
--   **Module navigation**
--
--   Module: [`KLS/BKL/CumulantEnergy/Basic`](https://prove2.me/theorems/4f12a1ef-12d3-46f5-b544-7dda9d084086).
--
--   Definition modules: [`Probability/Covariance/Basic`](https://prove2.me/theorems/c4e236b4-be51-468e-9de3-e2203fe87adc).
--
--   Supporting theorems: [`inverseSqrt_mul_mul_inverseSqrt`](https://prove2.me/theorems/88c3f67d-7fa1-4c20-b7d0-8fa8e80c182a).
--
--   Previous: [`sqrt_sum_sq_sum_le`](https://prove2.me/theorems/f159c409-0b24-4a71-8718-4a4409e0445e) · Next: [`sqrt_sum_lowerDrift_sq_le_aux`](https://prove2.me/theorems/6205a939-9cd4-490f-9fe8-892a2e4d1cda).
--
--   [Source excerpt, lines 385–398](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/BKL/CumulantEnergy/Basic.lean#L385-L398) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/BKL/CumulantEnergy/Basic.lean#L382-L430 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.BKL.CumulantEnergy.Basic`, declaration `FunctionalInequalities.KLS.BKL.sum_sq_pairTerm_ofFn_le`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_CumulantEnergy_Basic

open MeasureTheory
open scoped RealInnerProductSpace
variable {n : ℕ}

theorem FunctionalInequalities.KLS.BKL.sum_sq_pairTerm_ofFn_le_readable (ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin n)))
    (hc : IsCompact (ν : Measure (EuclideanSpace ℝ (Fin n))).support)
    (hA : IsUnit (Covariance.operator (ν : Measure (EuclideanSpace ℝ (Fin n)))))
    (hApos : ∀ v, v ≠ 0 → 0 < ⟪Covariance.operator (ν : Measure (EuclideanSpace ℝ (Fin n))) v, v⟫)
    {c c₂ : ℕ} (β : ℝ)
    (h100 : ∀ v : EuclideanSpace ℝ (Fin n),
      cumulantEnergy (ν : Measure (EuclideanSpace ℝ (Fin n))) c₂ v ≤
        β * ⟪Covariance.operator (ν : Measure (EuclideanSpace ℝ (Fin n))) v, v⟫)
    (u : EuclideanSpace ℝ (Fin n)) :
    ∑ J₁ : Fin c → Fin n, ∑ J₂ : Fin c₂ → Fin n,
      pairTerm (ν : Measure (EuclideanSpace ℝ (Fin n))) u
        (List.ofFn fun i => sigmaBasis (ν : Measure (EuclideanSpace ℝ (Fin n))) (J₁ i))
        (List.ofFn fun i => sigmaBasis (ν : Measure (EuclideanSpace ℝ (Fin n))) (J₂ i)) ≤
      β * cumulantEnergy (ν : Measure (EuclideanSpace ℝ (Fin n))) (c + 1) u := by sorry
