-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_LogConcave_Suspension_map_density_shift_scale_readable
-- name    : FunctionalInequalities.KLS.LogConcave.Suspension.map_density_shift_scale_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:18:20.668625+00:00
-- url     : https://prove2.me/theorems/09fdc8e8-bedc-44df-98aa-24cf3f553bd2
-- title:
--   Density Transformation Under A Fibrewise Shear
-- statement:
--   This technical lemma gives the density transformation for a fibrewise affine change of variables.
--
--   Let $A$ be a measurable space, let $\mu$ be an s-finite measure on $A$, let $F:A\to\mathbb R$ be measurable, let $\sigma\ne0$, and let $w:A\times\mathbb R\to[0,\infty]$ be measurable. Under the map
--   $$T(a,\eta)=\left(a,\frac{F(a)+\eta}{\sigma}\right),$$
--   the pushforward of the measure with density $w$ relative to $\mu\otimes ds$ is the measure with density
--   $$|\sigma|\,w(a,\sigma s-F(a)).$$
--   Equivalently,
--   $$((\mu\otimes ds).withDensity\,w).map(T)
--   =(\mu\otimes ds).withDensity\bigl((a,s)\mapsto|\sigma|w(a,\sigma s-F(a))\bigr).$$
--
--   The lemma records the Jacobian factor for the shear and rescaling used in the suspension density calculation.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.KLS.LogConcave.Suspension`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   private theorem map_density_shift_scale {A : Type*} [MeasurableSpace A] (μ : Measure A)
--       [SFinite μ] (F : A → ℝ) (hF : Measurable F) (σ : ℝ) (hσ : σ ≠ 0)
--       (w : A × ℝ → ENNReal) (hw : Measurable w) :
--       ((μ.prod volume).withDensity w).map (fun p => (p.1, (F p.1 + p.2) / σ)) =
--         (μ.prod volume).withDensity
--           (fun p => ENNReal.ofReal |σ| * w (p.1, σ * p.2 - F p.1))
--   ```
--
--   **Module navigation**
--
--   Module: [`KLS/BKL/Suspension/Density`](https://prove2.me/theorems/34f067f9-b370-4131-a2be-776da314cea2).
--
--   Next: [`jointLaw_eq_tilted`](https://prove2.me/theorems/a3adf66f-9b93-4f82-ab91-3e0f0b7f991d).
--
--   [Source excerpt, lines 29–34](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/BKL/Suspension/Density.lean#L29-L34) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/BKL/Suspension/Density.lean#L27-L79 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.BKL.Suspension.Density`, declaration `_private.FunctionalInequalities.KLS.BKL.Suspension.Density.0.FunctionalInequalities.KLS.LogConcave.Suspension.map_density_shift_scale`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_BKL_Suspension_Density

open MeasureTheory FunctionalInequalities.Probability.Line

theorem FunctionalInequalities.KLS.LogConcave.Suspension.map_density_shift_scale_readable {A : Type*} [MeasurableSpace A] (μ : Measure A)
    [SFinite μ] (F : A → ℝ) (hF : Measurable F) (σ : ℝ) (hσ : σ ≠ 0)
    (w : A × ℝ → ENNReal) (hw : Measurable w) :
    ((μ.prod volume).withDensity w).map (fun p => (p.1, (F p.1 + p.2) / σ)) =
      (μ.prod volume).withDensity
        (fun p => ENNReal.ofReal |σ| * w (p.1, σ * p.2 - F p.1)) := by sorry
