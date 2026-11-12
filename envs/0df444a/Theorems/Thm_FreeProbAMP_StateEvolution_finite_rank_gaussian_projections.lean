-- Prove2me | Theorems.Thm_FreeProbAMP_StateEvolution_finite_rank_gaussian_projections
-- name    : FreeProbAMP.StateEvolution.finite_rank_gaussian_projections
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T16:27:49.485763+00:00
-- url     : https://prove2.me/theorems/308706a5-dd34-4c86-92ff-e092449d4157
-- title:
--   Lemma 4.2 — finite-rank Gaussian projection estimates
-- statement:
--   For fixed finite column counts $p,q$, let $Q_d:\mathbb R^p\to H_{n(d)}$ and $R_d:\mathbb R^q\to K_d$ be random column maps, and let $h_d\in H_{n(d)}$ and $k_d\in K_d$ be random queries. A fresh GOE operator $\widetilde A_d$ is independent of all these data. No rank hypothesis is imposed. Conditionally on $(Q_d,R_d,h_d,k_d)$,
--
--   $$\|P_{R_d}\widetilde A_dh_d\|_{\rm op}=O_{\mathbb P}(d^{-1/2}\|h_d\|_n),\qquad
--   \|P_{Q_d}\widetilde A_d^*k_d\|_n=O_{\mathbb P}(d^{-1}\|k_d\|_{2,d}).$$
--
--   Conditionally on $h_d$, $\widetilde A_dh_d$ has law $\|h_d\|_n W_d$ for standard normalized GOE $W_d$. Conditionally on $k_d$, the coordinates of $\widetilde A_d^*k_d$ are independent centered normals with common variance $\alpha_d\|k_d\|_{2,d}^2$.
--
--   These estimates control finite-dimensional revealed projections. The tightness thresholds can depend on $p,q$ and the prescribed error probability, before the dimension and before the conditioning data; the proof's Gaussian variance calculation supplies this uniform conditional version. If either query is zero, its corresponding output is zero. No aspect-ratio limit is required by this lemma.
--
--   Differences from the source:
--   - encoding: positive matrix dimension d tends to infinity → natural index j represents physical dimension j+1; reason: bijection with all positive dimensions; n(j) remains arbitrary
--   - encoding: random vectors and matrix observations → explicit measurability of random data and almost-everywhere symmetry; reason: the standing random-variable convention is made explicit; no distribution is excluded
--   - encoding: sample sizes n(d) with n(d) → ∞ → n(d) ≥ 1 for every d; reason: nondegeneracy only; at n = 0 the source's 1/n and n^{-1/2} normalizations are undefined, and n(d) → ∞ leaves only finitely many such d, which no limit statement sees
--   - reading: conditionally on (Q, R, h, k), the norms are O_P of the stated scales → for each error level one threshold L and d₀ such that the exceedance has conditional probability at most the error level on every event of σ(Q, R, h, k); reason: the standard meaning of a conditional O_P statement, never weaker than the unconditional one; the proof's Gaussian variance bound is uniform in the conditioning data
-- source:
--   August Chen, Ahmed El Alaoui, STOC 2027 submission #1182 (October 2026), p. 27, Lemma 4.2 and proof

import Mathlib
import Definitions.Def_FreeProbAMP_StateEvolution_History

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology NNReal Matrix
set_option autoImplicit false
noncomputable section

namespace FreeProbAMP.StateEvolution

/-- Lemma 4.2, submission p.27; no full-rank hypothesis. -/
theorem finite_rank_gaussian_projections
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (n : ℕ → ℕ) (hn : ∀ d, 0 < n d) (p q : ℕ)
    (Q : (d : ℕ) → Ω → Fin p → Fin (n d) → ℝ)
    (R : (d : ℕ) → Ω → Fin q → RMat (d+1))
    (h : (d : ℕ) → Ω → Fin (n d) → ℝ) (k : (d : ℕ) → Ω → RMat (d+1))
    (A : (d : ℕ) → Ω → Fin (n d) → RMat (d+1))
    (hm : ∀ d, Measurable (Q d) ∧ Measurable (R d) ∧ Measurable (h d) ∧ Measurable (k d))
    (hs : ∀ d, ∀ᵐ ω ∂μ, (k d ω).transpose = k d ω ∧ ∀ j, (R d ω j).transpose = R d ω j)
    (hg : ∀ d, GOEArray μ (A d))
    (hi : ∀ d, Indep (sigma (A d)) (sigma (Q d) ⊔ sigma (R d) ⊔ sigma (h d) ⊔ sigma (k d)) μ) :
    ConditionalOP μ (fun d => sigma (Q d) ⊔ sigma (R d) ⊔ sigma (h d) ⊔ sigma (k d))
      (fun d ω => opNorm (spanProjection matInner (R d ω) (applyA (A d ω) (h d ω))))
      (fun d ω => (Real.sqrt (d+1))⁻¹ * vecNorm (h d ω)) ∧
    ConditionalOP μ (fun d => sigma (Q d) ⊔ sigma (R d) ⊔ sigma (h d) ⊔ sigma (k d))
      (fun d ω => vecNorm (spanProjection vecInner (Q d ω) (applyAdj (A d ω) (k d ω))))
      (fun d ω => (d+1 : ℝ)⁻¹ * matNorm2 (k d ω)) ∧
    (∀ d, ConditionalLaw μ (sigma (h d)) (fun ω => applyA (A d ω) (h d ω))
      (fun ω => (RandMatDisc.goe (d+1)).map (fun W => vecNorm (h d ω) • W))) ∧
    (∀ d, ConditionalLaw μ (sigma (k d)) (fun ω => applyAdj (A d ω) (k d ω))
      (fun ω => Measure.pi (fun _ : Fin (n d) => gaussianReal 0
        (⟨aspect (n d) (d+1) * matNorm2 (k d ω)^2,
          mul_nonneg (by unfold aspect; positivity) (sq_nonneg _)⟩ : ℝ≥0)))) := by sorry

end FreeProbAMP.StateEvolution
