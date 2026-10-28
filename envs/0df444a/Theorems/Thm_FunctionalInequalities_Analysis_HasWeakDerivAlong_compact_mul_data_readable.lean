-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_HasWeakDerivAlong_compact_mul_data_readable
-- name    : FunctionalInequalities.Analysis.HasWeakDerivAlong.compact_mul_data_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:02:51.055396+00:00
-- url     : https://prove2.me/theorems/14d1dc0b-7afe-403f-ae05-0178b771addc
-- title:
--   Localized Weak Product Data
-- statement:
--   This is a localized product rule that also supplies support and integrability information. It is listed as a partial formalization of Theorem 2.5 of Letwin (2026).
--
--   Let $n\in\mathbb{N}$, let $f,df:\mathrm{EuclideanSpace}\,\mathbb{R}\,(\mathrm{Fin}\,n)\to\mathbb{R}$, and let $v$ be a vector in the same space. Assume:
--
--   1. `HasWeakDerivAlong f df v`.
--   2. For every compact $S$, $df\in L^2(\operatorname{volume}|_S)$.
--   3. For every compact $S$, $f\in L^\infty(\operatorname{volume}|_S)$, expressed as `MemLp` with exponent $\top$.
--   4. $\psi$ is $C^1$ and compactly supported.
--
--   Then `HasWeakDerivAlong` holds for $\psi f$ with derivative
--
--   $$x\mapsto \psi(x)df(x)+D\psi(x)[v]f(x).$$
--
--   Moreover, both this product and its displayed weak derivative have compact support, and the derivative belongs globally to $L^2(\operatorname{volume})$. This packages the regularity properties needed for compactly supported testing.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem HasWeakDerivAlong.compact_mul_data {n : ℕ}
--       {f df : EuclideanSpace ℝ (Fin n) → ℝ} {v : EuclideanSpace ℝ (Fin n)}
--       (h : HasWeakDerivAlong f df v)
--       (hdf : ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
--         MemLp df 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S))
--       (hf : ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
--         MemLp f (⊤ : ENNReal) ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S))
--       {ψ : EuclideanSpace ℝ (Fin n) → ℝ}
--       (hψ : ContDiff ℝ 1 ψ) (hψc : HasCompactSupport ψ) :
--       HasWeakDerivAlong (fun x => ψ x * f x)
--         (fun x => ψ x * df x + fderiv ℝ ψ x v * f x) v ∧
--       HasCompactSupport (fun x => ψ x * f x) ∧
--       HasCompactSupport (fun x => ψ x * df x + fderiv ℝ ψ x v * f x) ∧
--       MemLp (fun x => ψ x * df x + fderiv ℝ ψ x v * f x) 2
--         (volume : Measure (EuclideanSpace ℝ (Fin n)))
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/WeakDerivative/Calculus`](https://prove2.me/theorems/e4287351-4501-4e28-b10c-d6fa6fcca9b5).
--
--   Definition modules: [`Analysis/WeakDerivative/Basic`](https://prove2.me/theorems/5af72772-2fc4-48c4-926f-dd1d449f0f11).
--
--   Supporting theorems: [`HasWeakDerivAlong.mul_contDiff`](https://prove2.me/theorems/2a566c7d-243e-41f1-be35-eae8ff92ebb5), [`memLp_mul_of_hasCompactSupport`](https://prove2.me/theorems/b04b1dc7-d732-49ae-8bbb-620873456903).
--
--   Previous: [`integral_flux_eq_neg_forcing_of_bounded_weak_test`](https://prove2.me/theorems/a62894bf-0470-4e04-8a24-6f8073da24d8) · Next: [`integral_compact_flux_eq_neg_forcing_of_global_bounded_weak_test`](https://prove2.me/theorems/68f53a73-98d0-4677-9ebd-c4a0016296fd).
--
--   [Source excerpt, lines 1355–1369](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/WeakDerivative/Calculus.lean#L1355-L1369) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/WeakDerivative/Calculus.lean#L1353-L1382 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.WeakDerivative.Calculus`, declaration `FunctionalInequalities.Analysis.HasWeakDerivAlong.compact_mul_data`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_WeakDerivative_Calculus

open MeasureTheory Set Filter

theorem FunctionalInequalities.Analysis.HasWeakDerivAlong.compact_mul_data_readable {n : ℕ}
    {f df : EuclideanSpace ℝ (Fin n) → ℝ} {v : EuclideanSpace ℝ (Fin n)}
    (h : HasWeakDerivAlong f df v)
    (hdf : ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
      MemLp df 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S))
    (hf : ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
      MemLp f (⊤ : ENNReal) ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S))
    {ψ : EuclideanSpace ℝ (Fin n) → ℝ}
    (hψ : ContDiff ℝ 1 ψ) (hψc : HasCompactSupport ψ) :
    HasWeakDerivAlong (fun x => ψ x * f x)
      (fun x => ψ x * df x + fderiv ℝ ψ x v * f x) v ∧
    HasCompactSupport (fun x => ψ x * f x) ∧
    HasCompactSupport (fun x => ψ x * df x + fderiv ℝ ψ x v * f x) ∧
    MemLp (fun x => ψ x * df x + fderiv ℝ ψ x v * f x) 2
      (volume : Measure (EuclideanSpace ℝ (Fin n))) := by sorry
