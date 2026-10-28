-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_CEK_hasDerivAt_integral_exp_neg_legendre_add_smul_readable
-- name    : FunctionalInequalities.KLS.CEK.hasDerivAt_integral_exp_neg_legendre_add_smul_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:05:27.798819+00:00
-- url     : https://prove2.me/theorems/302acb49-a8f6-47fd-812e-b58a38e4f610
-- title:
--   First Variation of the Conjugate Partition Function
-- statement:
--   This formalizes the integrated first-variation formula (42) in the proof of Theorem 2 of Cordero–Klartag (arXiv:1304.0630v1).
--
--   Let $E$ be finite-dimensional with Borel structure, let $q$ be proper and lower semicontinuous, and let $\psi:E\to\mathbb{R}$ satisfy $q^*(x)=\psi(x)$ for every $x$. Assume $\psi$ is $L$-Lipschitz for some $L\in[0,\infty)$ and $e^{-\psi}$ is integrable with respect to Lebesgue measure. Let $b:E\to\mathbb{R}$ be continuous and suppose $|b(z)|\le M$ for some $M\in\mathbb{R}$ and every $z$. Then
--
--   $$
--   t\longmapsto\int \exp\!\left(-\bigl(q+t b\bigr)^*(x).toReal\right)\,dx
--   $$
--
--   has derivative at $0$ equal to
--
--   $$
--   \int e^{-\psi(x)}\,b(\nabla\psi(x))\,dx.
--   $$
--
--   The gradient is the a.e. gradient represented by `gradient`; no stronger smoothness is asserted.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.KLS.CEK`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem hasDerivAt_integral_exp_neg_legendre_add_smul (q : E → EReal) (hq : ProperPotential q)
--       (hlsc : LowerSemicontinuous q) (ψ : E → ℝ) (hψ : ∀ x, legendre q x = (ψ x : EReal))
--       {L : NNReal} (hlip : LipschitzWith L ψ)
--       (hint : Integrable (fun x => Real.exp (-ψ x)) (volume : Measure E))
--       (b : E → ℝ) (hb : Continuous b) {M : ℝ} (hM : ∀ z, |b z| ≤ M) :
--       HasDerivAt
--         (fun t : ℝ => ∫ x, Real.exp (-(legendre (fun z => q z + ((t * b z : ℝ) : EReal)) x).toReal)
--           ∂(volume : Measure E))
--         (∫ x, Real.exp (-ψ x) * b (gradient ψ x) ∂(volume : Measure E)) 0
--   ```
--
--   **Module navigation**
--
--   Module: [`KLS/CEK/PartitionVariation`](https://prove2.me/theorems/e725e7ab-6aec-4f2c-8e87-f90cf0f5d355).
--
--   Definition modules: [`Analysis/Convex/Legendre`](https://prove2.me/theorems/ccf34d51-1332-4642-a3a3-dacdd0cbab81).
--
--   Supporting theorems: [`hasDerivAt_legendre_add_smul_of_dualDifferentiable`](https://prove2.me/theorems/53a6ee6c-57c2-4889-bf33-e52e9986092d), [`legendre_bounded_perturbation_finite_curve`](https://prove2.me/theorems/f81ed50e-1e1f-44d9-a9cd-afd086601533).
--
--   [Source excerpt, lines 31–39](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/CEK/PartitionVariation.lean#L31-L39) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/CEK/PartitionVariation.lean#L26-L241 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.CEK.PartitionVariation`, declaration `FunctionalInequalities.KLS.CEK.hasDerivAt_integral_exp_neg_legendre_add_smul`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_CEK_PartitionVariation

open MeasureTheory Set Metric
open FunctionalInequalities.Analysis
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem FunctionalInequalities.KLS.CEK.hasDerivAt_integral_exp_neg_legendre_add_smul_readable (q : E → EReal) (hq : ProperPotential q)
    (hlsc : LowerSemicontinuous q) (ψ : E → ℝ) (hψ : ∀ x, legendre q x = (ψ x : EReal))
    {L : NNReal} (hlip : LipschitzWith L ψ)
    (hint : Integrable (fun x => Real.exp (-ψ x)) (volume : Measure E))
    (b : E → ℝ) (hb : Continuous b) {M : ℝ} (hM : ∀ z, |b z| ≤ M) :
    HasDerivAt
      (fun t : ℝ => ∫ x, Real.exp (-(legendre (fun z => q z + ((t * b z : ℝ) : EReal)) x).toReal)
        ∂(volume : Measure E))
      (∫ x, Real.exp (-ψ x) * b (gradient ψ x) ∂(volume : Measure E)) 0 := by sorry
