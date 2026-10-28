-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_LogConcave_isBorellDensity_of_eq_tilted_readable
-- name    : FunctionalInequalities.KLS.LogConcave.isBorellDensity_of_eq_tilted_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:16:21.915517+00:00
-- url     : https://prove2.me/theorems/0d7194a7-857d-46cc-b91c-8366be9b61de
-- title:
--   Continuous Convex Tilt Gives a Borell Density
-- statement:
--   This formalizes the density description of a continuous convex tilt.
--
--   Let $V$ be a real inner-product normed space with Borel measurable structure, let $\nu$ be a probability measure, let $m$ be a measure, and let $W:V\to\mathbb R$. Assume:
--
--   1. $\nu=m.\mathrm{tilted}(-W)$;
--   2. $W$ is continuous;
--   3. $W$ is convex on all of $V$.
--
--   Then $\nu$ is a Borell density with respect to $m$ whose density is
--
--   $$x\longmapsto \frac{e^{-W(x)}}{\int_V e^{-W(y)}\,dm(y)}.$$
--
--   In particular, the density is measurable, nonnegative, upper semicontinuous, and log-concave. This is the density-theoretic interface between tilted measures and log-concave laws.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.KLS.LogConcave`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem isBorellDensity_of_eq_tilted {m : Measure V} {W : V → ℝ}
--       (hνW : (ν : Measure V) = m.tilted (-W)) (hW : Continuous W)
--       (hconv : ConvexOn ℝ Set.univ W) :
--       IsBorellDensity (ν : Measure V) m (fun x => Real.exp (-W x) / ∫ y, Real.exp (-W y) ∂m)
--   ```
--
--   **Module navigation**
--
--   Module: [`KLS/LogConcave/Density/Tilted`](https://prove2.me/theorems/93c40365-725a-495d-8823-167e1b658f38).
--
--   Definition modules: [`KLS/LogConcave/Density/BorellRepresentation/Basic`](https://prove2.me/theorems/b8e5cf48-3e73-4397-8358-4204a7803548).
--
--   Supporting theorems: [`integral_exp_neg_pos_of_eq_tilted`](https://prove2.me/theorems/fb765bf9-81da-4922-b614-0b50e7223f1c), [`rpow_mul_rpow_le_of_convexOn`](https://prove2.me/theorems/60c904f9-1850-43a9-b676-71efcb52afb5).
--
--   Previous: [`rpow_mul_rpow_le_of_convexOn`](https://prove2.me/theorems/60c904f9-1850-43a9-b676-71efcb52afb5) · Next: [`interior_support_nonempty_of_eq_tilted`](https://prove2.me/theorems/f9e547f0-9041-4fe6-9d08-ab4991b4217f).
--
--   [Source excerpt, lines 122–125](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/LogConcave/Density/Tilted.lean#L122-L125) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/LogConcave/Density/Tilted.lean#L119-L139 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.LogConcave.Density.Tilted`, declaration `FunctionalInequalities.KLS.LogConcave.isBorellDensity_of_eq_tilted`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_Density_Tilted

open MeasureTheory Set
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] {ν : MeasureTheory.ProbabilityMeasure V}
omit [FiniteDimensional ℝ V]

theorem FunctionalInequalities.KLS.LogConcave.isBorellDensity_of_eq_tilted_readable {m : Measure V} {W : V → ℝ}
    (hνW : (ν : Measure V) = m.tilted (-W)) (hW : Continuous W)
    (hconv : ConvexOn ℝ Set.univ W) :
    IsBorellDensity (ν : Measure V) m (fun x => Real.exp (-W x) / ∫ y, Real.exp (-W y) ∂m) := by sorry
