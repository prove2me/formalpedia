-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_integral_trace_quadratic_flux_eq_neg_density_readable
-- name    : FunctionalInequalities.Analysis.integral_trace_quadratic_flux_eq_neg_density_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:06:12.893405+00:00
-- url     : https://prove2.me/theorems/62d73344-315c-46bd-b8d0-841a9bad507d
-- title:
--   Weak Trace Quadratic Flux Identity
-- statement:
--   This formalizes the weak counterpart of Lemma 2.4, equations (2.8) and (2.10), of Letwin (arXiv:2607.24164v1), cited in relation to Theorem 2.5.
--
--   Let n be a natural number and work on $E=\operatorname{EuclideanSpace}\,\mathbb R\,(\operatorname{Fin} n)$. Let B be a constant matrix, H,R,E be matrix fields, T a field of matrix-valued tensor slices, and ρ a continuous scalar weight. Assume
--
--   1. every entry of H is in $L^\infty$ with respect to volume;
--   2. every entry of T is locally in $L^2$ on compact sets;
--   3. every entry of $\sum_bR_{ba}T_b$ is locally in $L^2$ on compact sets;
--   4. every entry of E is locally integrable; and
--   5. for every compactly supported C¹ test ψ and every l,k,i,j, the stated coordinate weak identity holds:
--      $$\int ρ\sum_a\left(\sum_bR_{ba}T_{b,ij}\right)\left(ψT_{a,lk}+D_{e_a}ψ\,H_{lk}\right)\,dx
--      =-\int ρE_{ij}ψH_{lk}\,dx.$$
--
--   Define
--
--   $$a(x,i)=2\operatorname{tr}(BH(x)B T(x,i)),$$
--
--   and
--
--   $$g(x)=2\operatorname{tr}(BH(x)BE(x))+2\sum_{i,j}R(x,i,j)\operatorname{tr}(BT(x,i)BT(x,j)).$$
--
--   Then g is locally integrable. For every compactly supported C¹ test ψ, the relevant flux terms and density term are integrable, and
--
--   $$\int ρ\sum_j\left(\sum_iR_{ij}a_i\right)D_{e_j}ψ\,dx
--   =-\int ρgψ\,dx.$$
--
--   This is the public weak trace-contraction theorem for rough finite-dimensional matrix fields; it does not itself assume a Hessian, potential, or source interpretation.
--
--   **Original Lean conclusion excerpt**
--
--   Within namespace `FunctionalInequalities.Analysis`. Shown in its original module context. Earlier hypotheses and the proof are omitted from this excerpt; the complete verified statement remains below.
--
--   ```lean
--       ∀ ψ : EuclideanSpace ℝ (Fin n) → ℝ,
--         ContDiff ℝ 1 ψ → HasCompactSupport ψ →
--         Integrable (fun x => ρ x * g x * ψ x)
--           (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
--         (∀ j : Fin n, Integrable (fun x => ρ x *
--           (∑ i : Fin n, R x i j * a x i) *
--           fderiv ℝ ψ x (EuclideanSpace.basisFun (Fin n) ℝ j))
--           (volume : Measure (EuclideanSpace ℝ (Fin n)))) ∧
--         (∫ x, ρ x * (∑ j : Fin n, (∑ i : Fin n, R x i j * a x i) *
--           fderiv ℝ ψ x (EuclideanSpace.basisFun (Fin n) ℝ j))
--           ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
--         -(∫ x, ρ x * g x * ψ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n))))
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/Matrix/WeakTrace`](https://prove2.me/theorems/4921a24d-b044-4852-b95d-96829251045f).
--
--   Supporting theorems: [`trace_mul_mul_mul_eq_sum`](https://prove2.me/theorems/341ba53c-b3cb-4ad0-873d-9d84885a6c75), [`integral_trace_contraction_of_coordinate_pairings`](https://prove2.me/theorems/95e16cb2-bd29-4841-b725-9353894707a0).
--
--   Previous: [`integral_trace_contraction_of_coordinate_pairings`](https://prove2.me/theorems/95e16cb2-bd29-4841-b725-9353894707a0).
--
--   [Source excerpt, lines 354–365](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Matrix/WeakTrace.lean#L354-L365) · Frozen source `408915f`.
-- source:
--   Source: Letwin, The KLS constant is O(log^(1/4) n) (arXiv:2607.24164v1), Theorem 2.5. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Matrix/WeakTrace.lean#L321-L479 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Matrix.WeakTrace`, declaration `FunctionalInequalities.Analysis.integral_trace_quadratic_flux_eq_neg_density`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Matrix_WeakTrace

open MeasureTheory Filter Set Matrix
set_option maxHeartbeats 1000000

theorem FunctionalInequalities.Analysis.integral_trace_quadratic_flux_eq_neg_density_readable {n : ℕ}
    (B : Matrix (Fin n) (Fin n) ℝ)
    (H R E : EuclideanSpace ℝ (Fin n) → Matrix (Fin n) (Fin n) ℝ)
    (T : EuclideanSpace ℝ (Fin n) → Fin n → Matrix (Fin n) (Fin n) ℝ)
    (ρ : EuclideanSpace ℝ (Fin n) → ℝ)
    (hρ : Continuous ρ)
    (hH : ∀ i j : Fin n, MemLp (fun x => H x i j) (⊤ : ENNReal)
      (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hT : ∀ a i j : Fin n, ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
      MemLp (fun x => T x a i j) 2
        ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S))
    (hJ : ∀ i j a : Fin n, ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
      MemLp (fun x => ∑ b : Fin n, R x b a * T x b i j) 2
        ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S))
    (hE : ∀ i j : Fin n, LocallyIntegrable (fun x => E x i j)
      (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hTest : ∀ ψ : EuclideanSpace ℝ (Fin n) → ℝ,
      ContDiff ℝ 1 ψ → HasCompactSupport ψ → ∀ l k i j : Fin n,
      (∫ x, ρ x * (∑ a : Fin n, (∑ b : Fin n, R x b a * T x b i j) *
        (ψ x * T x a l k +
          fderiv ℝ ψ x (EuclideanSpace.basisFun (Fin n) ℝ a) * H x l k))
        ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
      -(∫ x, ρ x * E x i j * (ψ x * H x l k)
        ∂(volume : Measure (EuclideanSpace ℝ (Fin n))))) :
    let a := fun x i => 2 * (B * H x * B * T x i).trace
    let g := fun x => 2 * (B * H x * B * E x).trace +
      2 * ∑ i : Fin n, ∑ j : Fin n, R x i j * (B * T x i * B * T x j).trace
    LocallyIntegrable g (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
    ∀ ψ : EuclideanSpace ℝ (Fin n) → ℝ,
      ContDiff ℝ 1 ψ → HasCompactSupport ψ →
      Integrable (fun x => ρ x * g x * ψ x)
        (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
      (∀ j : Fin n, Integrable (fun x => ρ x *
        (∑ i : Fin n, R x i j * a x i) *
        fderiv ℝ ψ x (EuclideanSpace.basisFun (Fin n) ℝ j))
        (volume : Measure (EuclideanSpace ℝ (Fin n)))) ∧
      (∫ x, ρ x * (∑ j : Fin n, (∑ i : Fin n, R x i j * a x i) *
        fderiv ℝ ψ x (EuclideanSpace.basisFun (Fin n) ℝ j))
        ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
      -(∫ x, ρ x * g x * ψ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) := by sorry
