-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_integral_weakDeriv_mul_eq_swap_readable
-- name    : FunctionalInequalities.Analysis.integral_weakDeriv_mul_eq_swap_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:05:34.951464+00:00
-- url     : https://prove2.me/theorems/61cf322f-0c0f-4f7d-8765-ac88a842a6c5
-- title:
--   Weak Derivative Curl Identity
-- statement:
--   This is a compact-support weak integration-by-parts identity for two directional derivatives of the same scalar function.
--
--   Let $f$ have weak derivatives $p$ and $q$ along directions $v$ and $w$, respectively, with $p$ and $q$ locally in $L^2$. Let $\eta$ have weak derivatives $a$ and $b$ along $v$ and $w$, respectively. Assume $\eta,a,b$ have compact support and $a,b$ are globally in $L^2$. Then
--
--   $$
--   \int p(x)b(x)\,dx=\int q(x)a(x)\,dx.
--   $$
--
--   The identity is valid in every finite dimension, including dimension zero, and is a supporting rough-testing statement.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem integral_weakDeriv_mul_eq_swap {n : ℕ}
--       {f p q η a b : EuclideanSpace ℝ (Fin n) → ℝ}
--       {v w : EuclideanSpace ℝ (Fin n)}
--       (hp : HasWeakDerivAlong f p v) (hq : HasWeakDerivAlong f q w)
--       (hp2 : ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
--         MemLp p 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S))
--       (hq2 : ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
--         MemLp q 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S))
--       (hηv : HasWeakDerivAlong η a v) (hηw : HasWeakDerivAlong η b w)
--       (hηc : HasCompactSupport η) (hac : HasCompactSupport a) (hbc : HasCompactSupport b)
--       (ha2 : MemLp a 2 (volume : Measure (EuclideanSpace ℝ (Fin n))))
--       (hb2 : MemLp b 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) :
--       (∫ x, p x * b x ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
--         ∫ x, q x * a x ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/WeakDerivative/Calculus`](https://prove2.me/theorems/e4287351-4501-4e28-b10c-d6fa6fcca9b5).
--
--   Definition modules: [`Analysis/WeakDerivative/Basic`](https://prove2.me/theorems/5af72772-2fc4-48c4-926f-dd1d449f0f11).
--
--   Supporting theorems: [`exists_contDiff_compact_weak_deriv_approximation`](https://prove2.me/theorems/2972130c-74ad-41b7-aa1b-dec182289761).
--
--   Previous: [`HasWeakDerivAlong.mul_of_locally_bounded`](https://prove2.me/theorems/1133273b-c737-4c38-bf2a-2953cd23a941) · Next: [`compact_bounded_test_domination`](https://prove2.me/theorems/598f7c40-05a7-49e8-94fe-b29d9620425b).
--
--   [Source excerpt, lines 833–846](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/WeakDerivative/Calculus.lean#L833-L846) · Frozen source `408915f`.
-- source:
--   Source: Letwin, The KLS constant is O(log^(1/4) n) (arXiv:2607.24164v1), Lemma 2.4. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/WeakDerivative/Calculus.lean#L830-L1076 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.WeakDerivative.Calculus`, declaration `FunctionalInequalities.Analysis.integral_weakDeriv_mul_eq_swap`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_WeakDerivative_Calculus

open MeasureTheory Filter Set Metric InnerProductSpace
set_option maxHeartbeats 800000

theorem FunctionalInequalities.Analysis.integral_weakDeriv_mul_eq_swap_readable {n : ℕ}
    {f p q η a b : EuclideanSpace ℝ (Fin n) → ℝ}
    {v w : EuclideanSpace ℝ (Fin n)}
    (hp : HasWeakDerivAlong f p v) (hq : HasWeakDerivAlong f q w)
    (hp2 : ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
      MemLp p 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S))
    (hq2 : ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
      MemLp q 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S))
    (hηv : HasWeakDerivAlong η a v) (hηw : HasWeakDerivAlong η b w)
    (hηc : HasCompactSupport η) (hac : HasCompactSupport a) (hbc : HasCompactSupport b)
    (ha2 : MemLp a 2 (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hb2 : MemLp b 2 (volume : Measure (EuclideanSpace ℝ (Fin n)))) :
    (∫ x, p x * b x ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
      ∫ x, q x * a x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))) := by sorry
