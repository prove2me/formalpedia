-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_LogConcave_integrable_exp_neg_of_eq_tilted_readable
-- name    : FunctionalInequalities.KLS.LogConcave.integrable_exp_neg_of_eq_tilted_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:13:20.507427+00:00
-- url     : https://prove2.me/theorems/df26f9df-caa5-4567-8468-df64dde52e70
-- title:
--   Integrability From a Probability Tilt Representation
-- statement:
--   This is an integrability consequence of a tilted probability representation.
--
--   Let $V$ be a measurable space, let $m$ be a measure on $V$, let $W:V\to\mathbb R$, and let $\nu$ be a probability measure. If
--
--   $$\nu=m.\operatorname{tilted}(-W),$$
--
--   then the unnormalized density is integrable:
--
--   $$x\longmapsto e^{-W(x)}\quad\text{is integrable with respect to }m.$$
--
--   No normed-space, finite-dimensional, or Borel assumptions are required by the type. The conclusion uses that a tilted measure identified with a probability measure cannot arise from a nonintegrable density.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.KLS.LogConcave`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem integrable_exp_neg_of_eq_tilted {m : Measure V} {W : V → ℝ}
--       (hνW : (ν : Measure V) = m.tilted (-W)) :
--       Integrable (fun x => Real.exp (-W x)) m
--   ```
--
--   **Module navigation**
--
--   Module: [`KLS/LogConcave/Density/Tilted`](https://prove2.me/theorems/93c40365-725a-495d-8823-167e1b658f38).
--
--   Next: [`integral_exp_neg_pos_of_eq_tilted`](https://prove2.me/theorems/fb765bf9-81da-4922-b614-0b50e7223f1c).
--
--   [Source excerpt, lines 30–32](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/KLS/LogConcave/Density/Tilted.lean#L30-L32) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/LogConcave/Density/Tilted.lean#L28-L45 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.LogConcave.Density.Tilted`, declaration `FunctionalInequalities.KLS.LogConcave.integrable_exp_neg_of_eq_tilted`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_KLS_LogConcave_Density_Tilted

open MeasureTheory Set
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] {ν : MeasureTheory.ProbabilityMeasure V}
omit [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [BorelSpace V]

theorem FunctionalInequalities.KLS.LogConcave.integrable_exp_neg_of_eq_tilted_readable {m : Measure V} {W : V → ℝ}
    (hνW : (ν : Measure V) = m.tilted (-W)) :
    Integrable (fun x => Real.exp (-W x)) m := by sorry
