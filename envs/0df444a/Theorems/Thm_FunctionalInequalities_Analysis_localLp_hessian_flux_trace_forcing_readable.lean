-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_localLp_hessian_flux_trace_forcing_readable
-- name    : FunctionalInequalities.Analysis.localLp_hessian_flux_trace_forcing_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:05:47.829376+00:00
-- url     : https://prove2.me/theorems/0d14ed2a-5f26-4feb-914f-b0d0e87bf35c
-- title:
--   Local Hessian Flux and Trace Forcing Bounds
-- statement:
--   This is a technical compact-local integrability statement for weak Hessian evolution.
--
--   Let $u:\mathbb{R}^n\to\mathbb{R}$ and let $T$ have compact-local $L^2$ components. Assume the inverse-Hessian derivatives
--
--   $$
--   -\bigl(H_u^{-1}T_kH_u^{-1}\bigr)_{ij}
--   $$
--
--   are compact-locally in $L^2$, the inverse-Hessian entries are compact-locally in $L^{\infty}$, and let $Q_{ij}$ be locally integrable. Define
--
--   $$
--   J_{ija}=\sum_b(H_u^{-1})_{ba}T_{bij},
--   $$
--
--   and
--
--   $$
--   C_{ij}=Q_{ij}-\sum_{a,b}T_{iab}D_{jba}+\sum_bT_{bij}\sum_aD_{aba},
--   $$
--
--   where $D_{kba}=-(H_u^{-1}T_kH_u^{-1})_{ba}$. Then, for every $i,j$, each $J_{ija}$ belongs locally to $L^2$ on compact sets and $C_{ij}$ is locally integrable. This conclusion is purely analytic and assumes no classical Hessian regularity.
--
--   **Original Lean conclusion excerpt**
--
--   Within namespace `FunctionalInequalities.Analysis`. Shown in its original module context. Earlier hypotheses and the proof are omitted from this excerpt; the complete verified statement remains below.
--
--   ```lean
--       let R := fun x => (hessianMatrix u x)⁻¹
--       let D := fun x k b a => -((R x * (Matrix.of fun c d => T x k c d) * R x) b a)
--       let J := fun x i j a => ∑ b : Fin n, R x b a * T x b i j
--       let C := fun x i j => Q x i j -
--         (∑ a : Fin n, ∑ b : Fin n, T x i a b * D x j b a) +
--         ∑ b : Fin n, T x b i j * (∑ a : Fin n, D x a b a)
--       ∀ i j : Fin n,
--         (∀ a : Fin n, ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
--           MemLp (fun x => J x i j a) 2
--             ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) ∧
--         LocallyIntegrable (fun x => C x i j)
--           (volume : Measure (EuclideanSpace ℝ (Fin n)))
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/BakryEmery/IntegrationByParts/WeakHessianEvolution`](https://prove2.me/theorems/d20d941d-a690-4ebe-9a63-a346adf8dd16).
--
--   Definition modules: [`Analysis/BakryEmery/HessianOperator`](https://prove2.me/theorems/0a60d77a-9d99-47ed-a649-6e1a28e13392), [`Analysis/Operator/Coordinates`](https://prove2.me/theorems/104936bd-b536-4e43-8bdb-e45d2e66c788).
--
--   Previous: [`hasWeakDerivAlong_mongeAmpere_first_rhs`](https://prove2.me/theorems/55f12f10-6c36-4776-96b3-387313b3b590) · Next: [`integral_array_pair_balance`](https://prove2.me/theorems/6a56d72a-b125-4b6e-9809-d8d6e98e7bf3).
--
--   [Source excerpt, lines 491–502](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/BakryEmery/IntegrationByParts/WeakHessianEvolution.lean#L491-L502) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/BakryEmery/IntegrationByParts/WeakHessianEvolution.lean#L472-L551 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.BakryEmery.IntegrationByParts.WeakHessianEvolution`, declaration `FunctionalInequalities.Analysis.localLp_hessian_flux_trace_forcing`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_IntegrationByParts_WeakHessianEvolution

open MeasureTheory Set Filter
open FunctionalInequalities.Probability.Stein
set_option maxHeartbeats 800000

theorem FunctionalInequalities.Analysis.localLp_hessian_flux_trace_forcing_readable {n : ℕ}
    {u : EuclideanSpace ℝ (Fin n) → ℝ}
    (T : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → Fin n → ℝ)
    (hT2 : ∀ k i j : Fin n, ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
      MemLp (fun x => T x k i j) 2
        ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S))
    (hInv2 : ∀ k i j : Fin n, ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
      MemLp (fun x => -(((hessianMatrix u x)⁻¹ *
        (Matrix.of fun a b => T x k a b) * (hessianMatrix u x)⁻¹) i j)) 2
        ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S))
    (hRtop : ∀ i j : Fin n, ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
      MemLp (fun x => (hessianMatrix u x)⁻¹ i j) (⊤ : ENNReal)
        ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S))
    (Q : EuclideanSpace ℝ (Fin n) → Fin n → Fin n → ℝ)
    (hQ : ∀ i j : Fin n, LocallyIntegrable (fun x => Q x i j)
      (volume : Measure (EuclideanSpace ℝ (Fin n)))) :
    let R := fun x => (hessianMatrix u x)⁻¹
    let D := fun x k b a => -((R x * (Matrix.of fun c d => T x k c d) * R x) b a)
    let J := fun x i j a => ∑ b : Fin n, R x b a * T x b i j
    let C := fun x i j => Q x i j -
      (∑ a : Fin n, ∑ b : Fin n, T x i a b * D x j b a) +
      ∑ b : Fin n, T x b i j * (∑ a : Fin n, D x a b a)
    ∀ i j : Fin n,
      (∀ a : Fin n, ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
        MemLp (fun x => J x i j a) 2
          ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) ∧
      LocallyIntegrable (fun x => C x i j)
        (volume : Measure (EuclideanSpace ℝ (Fin n))) := by sorry
