-- Prove2me | Theorems.Thm_LevyStochCalc_Brownian_Ito_SimplePredictable_exists_restrict_Ioc_readable
-- name    : LevyStochCalc.Brownian.Ito.SimplePredictable.exists_restrict_Ioc_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:08:59.0508+00:00
-- url     : https://prove2.me/theorems/5e9d641c-78ce-4154-aba8-1c8bbbf578e0
-- title:
--   Restriction of a Simple Predictable Integrand to an Interval
-- statement:
--   This theorem establishes existence of a simple predictable representation restricted to the interval $(a,b]$.
--
--   Let $P$ be a probability measure, $W$ a Brownian motion, and $\mathcal F$ a filtration. Let $G$ be a simple predictable integrand whose coefficients are strongly measurable with respect to the sigma-algebra at the left endpoint of each tile. Assume:
--
--   1. $C\ge0$;
--   2. every coefficient of $G$ has absolute value at most $C$;
--   3. $0\le a<b$.
--
--   Then there exist a real horizon $T_3$ and a simple predictable integrand $Q$ such that its coefficients are adapted and strongly measurable, its evaluation is the restriction of $G$ to $(a,b]$,
--
--   $$
--   Q.\operatorname{eval}(s,\omega)=\mathbf 1_{(a,b]}(s)\,G.\operatorname{eval}(s,\omega),
--   $$
--
--   and every coefficient $\xi^Q_j(\omega)$ satisfies
--
--   $$
--   |\xi^Q_j(\omega)|\le
--   \begin{cases}
--   C,&a\le \tau^Q_{j}\text{ and }\tau^Q_{j+1}\le b,\\
--   0,&\text{otherwise.}
--   \end{cases}
--   $$
--
--   The construction is provided by `SimplePredictable.exists_restrict_Ioc_readable` and is useful for localizing elementary Itô integrands while retaining adaptation and coefficient bounds.
--
--   **Original Lean declaration header**
--
--   Within namespace `LevyStochCalc.Brownian.Ito`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem SimplePredictable.exists_restrict_Ioc
--       {P : Measure Ω} [IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)
--       (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
--       {T : ℝ} (G : SimplePredictable Ω T)
--       (h_adapt : ∀ i : Fin G.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
--         (ℱ (G.partition i.castSucc)) (G.ξ i))
--       {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ (i : Fin G.N) (ω : Ω), |G.ξ i ω| ≤ C)
--       {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
--       ∃ (T₃ : ℝ) (Q : SimplePredictable Ω T₃),
--         (∀ i : Fin Q.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
--           (ℱ (Q.partition i.castSucc)) (Q.ξ i))
--         ∧ (∀ s ω, Q.eval s ω = (Set.Ioc a b).indicator (fun _ => (1 : ℝ)) s * G.eval s ω)
--         ∧ (∀ (j : Fin Q.N) (ω : Ω), |Q.ξ j ω|
--             ≤ if a ≤ Q.partition j.castSucc ∧ Q.partition j.succ ≤ b then C else 0)
--   ```
--
--   **Module navigation**
--
--   Module: [`LevyStochCalc/Brownian/ItoIncrementMomentRestrict`](https://prove2.me/theorems/6729fab9-4d54-4cac-a286-3a20b472164d).
--
--   Definition modules: [`LevyStochCalc/Brownian/ItoSimpleIntegrand`](https://prove2.me/theorems/09c8ba67-9427-4d17-9c39-a5ddcdf07edb), [`LevyStochCalc/Brownian/Construction`](https://prove2.me/theorems/742cb048-99b1-4e53-bf9d-ffd292ffaaa3).
--
--   Supporting theorems: [`SimplePredictable.abs_eval_le`](https://prove2.me/theorems/1cd600b6-5e8b-4337-a77d-6ea63c207357), [`SimplePredictable.exists_mul_simple`](https://prove2.me/theorems/2d890f64-d894-41e2-b8b4-bc4a0edaf483), [`stepIoc_eval`](https://prove2.me/theorems/229a87fb-276d-451b-880f-3ee228acc687), [`stepIoc₀_eval`](https://prove2.me/theorems/2c0d5744-8278-417f-9f9c-dd287d9c0a4f).
--
--   Previous: [`SimplePredictable.varClock_le_Ioc`](https://prove2.me/theorems/439559a5-0cc2-4a3a-a3c2-a6d24460420f).
--
--   [Source excerpt, lines 184–197](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Brownian/ItoIncrementMomentRestrict.lean#L184-L197) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Brownian/ItoIncrementMomentRestrict.lean#L180-L236 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Brownian.ItoIncrementMomentRestrict`, declaration `LevyStochCalc.Brownian.Ito.SimplePredictable.exists_restrict_Ioc`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoIncrementMomentRestrict

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ItoIncrementMomentRestrict.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory
universe u
variable {Ω : Type u} [MeasurableSpace Ω]

theorem LevyStochCalc.Brownian.Ito.SimplePredictable.exists_restrict_Ioc_readable
    {P : Measure Ω} [IsProbabilityMeasure P] (W : LevyStochCalc.Brownian.BrownianMotion P)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›)
    {T : ℝ} (G : SimplePredictable Ω T)
    (h_adapt : ∀ i : Fin G.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ (G.partition i.castSucc)) (G.ξ i))
    {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ (i : Fin G.N) (ω : Ω), |G.ξ i ω| ≤ C)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    ∃ (T₃ : ℝ) (Q : SimplePredictable Ω T₃),
      (∀ i : Fin Q.N, @MeasureTheory.StronglyMeasurable Ω ℝ _
        (ℱ (Q.partition i.castSucc)) (Q.ξ i))
      ∧ (∀ s ω, Q.eval s ω = (Set.Ioc a b).indicator (fun _ => (1 : ℝ)) s * G.eval s ω)
      ∧ (∀ (j : Fin Q.N) (ω : Ω), |Q.ξ j ω|
          ≤ if a ≤ Q.partition j.castSucc ∧ Q.partition j.succ ≤ b then C else 0) := by sorry
