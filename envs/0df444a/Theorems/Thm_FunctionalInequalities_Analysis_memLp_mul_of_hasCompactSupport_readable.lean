-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_memLp_mul_of_hasCompactSupport_readable
-- name    : FunctionalInequalities.Analysis.memLp_mul_of_hasCompactSupport_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:02:49.4531+00:00
-- url     : https://prove2.me/theorems/b04b1dc7-d732-49ae-8bbb-620873456903
-- title:
--   Compactly Supported Cutoff Preserves Global $L^2$ Integrability
-- statement:
--   This statement shows that a compactly supported cutoff converts local $L^2$ control into global $L^2$ control.
--
--   Let $n\in\mathbb{N}$ and let $f,\chi:\mathrm{EuclideanSpace}\,\mathbb{R}\,(\mathrm{Fin}\,n)\to\mathbb{R}$. Assume that $\chi$ is continuous and compactly supported. Assume also that, for every compact set $S$, the restriction of $f$ to $S$ belongs to $L^2$ with respect to restricted Lebesgue measure:
--
--   $$f\in L^2(\operatorname{volume}|_S).$$
--
--   Then
--
--   $$\chi f\in L^2(\operatorname{volume}).$$
--
--   The exponent is the Lean `MemLp` exponent $2$, and the conclusion uses the full volume measure. This is a reusable localization lemma.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem memLp_mul_of_hasCompactSupport {n : ℕ}
--       {f χ : EuclideanSpace ℝ (Fin n) → ℝ}
--       (hχ : Continuous χ) (hχc : HasCompactSupport χ)
--       (hf : ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
--         MemLp f 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) :
--       MemLp (fun x => χ x * f x) 2
--         (volume : Measure (EuclideanSpace ℝ (Fin n)))
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/WeakDerivative/Calculus`](https://prove2.me/theorems/e4287351-4501-4e28-b10c-d6fa6fcca9b5).
--
--   Previous: [`HasWeakDerivAlong.mul_of_memLp_two`](https://prove2.me/theorems/194c1651-5c29-4beb-84c6-06fd15f07790) · Next: [`HasWeakDerivAlong.mul_of_locally_memLp_two`](https://prove2.me/theorems/4c31865f-283b-4c42-8cee-41884d14d427).
--
--   [Source excerpt, lines 186–192](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/WeakDerivative/Calculus.lean#L186-L192) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/WeakDerivative/Calculus.lean#L185-L207 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.WeakDerivative.Calculus`, declaration `FunctionalInequalities.Analysis.memLp_mul_of_hasCompactSupport`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_WeakDerivative_Calculus

open MeasureTheory Filter Set Metric InnerProductSpace

theorem FunctionalInequalities.Analysis.memLp_mul_of_hasCompactSupport_readable {n : ℕ}
    {f χ : EuclideanSpace ℝ (Fin n) → ℝ}
    (hχ : Continuous χ) (hχc : HasCompactSupport χ)
    (hf : ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
      MemLp f 2 ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S)) :
    MemLp (fun x => χ x * f x) 2
      (volume : Measure (EuclideanSpace ℝ (Fin n))) := by sorry
