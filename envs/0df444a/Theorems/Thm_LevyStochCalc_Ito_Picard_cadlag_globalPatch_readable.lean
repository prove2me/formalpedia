-- Prove2me | Theorems.Thm_LevyStochCalc_Ito_Picard_cadlag_globalPatch_readable
-- name    : LevyStochCalc.Ito.Picard.cadlag_globalPatch_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:13:04.368551+00:00
-- url     : https://prove2.me/theorems/3d125985-be22-4ea3-8cfc-9c8457d42cde
-- title:
--   Càdlàg Regularity of the Global Window Patch
-- statement:
--   This states that a global patch of compatible window paths is almost surely càdlàg on the nonnegative time domain.
--
--   Let $Y_k:\mathbb R\to\Omega\to\mathbb R^n$. Assume: (1) almost surely, `globalPatch Y` agrees with $Y_k$ on $[0,k+1]$ for every $k$; and (2) almost surely, each $Y_k$ is right-continuous and every coordinate has a left limit at every time.
--
--   Then, almost surely, for every $t\ge0$, the global patch is right-continuous at $t$ and each coordinate has a left limit:
--
--   $$\lim_{s\downarrow t}\operatorname{globalPatch}(Y,s,\omega)=\operatorname{globalPatch}(Y,t,\omega),$$
--
--   and for every $i<n$ there exists $\ell\in\mathbb R$ with
--   $$\lim_{s\uparrow t}\operatorname{globalPatch}(Y,s,\omega,i)=\ell.$$
--
--   The conclusion is restricted to $t\ge0$ and is an almost-everywhere path property.
--
--   **Original Lean declaration header**
--
--   Within namespace `LevyStochCalc.Ito.Picard`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem cadlag_globalPatch {Y : ℕ → ℝ → Ω → (Fin n → ℝ)}
--       (hagree : ∀ᵐ ω ∂P, ∀ k : ℕ, ∀ t ∈ Set.Icc (0 : ℝ) ((k : ℝ) + 1),
--         globalPatch Y t ω = Y k t ω)
--       (hYcad : ∀ k, ∀ᵐ ω ∂P, ∀ t : ℝ,
--         Filter.Tendsto (fun s => Y k s ω) (nhdsWithin t (Set.Ioi t)) (nhds (Y k t ω))
--           ∧ ∀ i : Fin n, ∃ ℓ : ℝ,
--               Filter.Tendsto (fun s => Y k s ω i) (nhdsWithin t (Set.Iio t)) (nhds ℓ)) :
--       ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t →
--         Filter.Tendsto (fun s => globalPatch Y s ω) (nhdsWithin t (Set.Ioi t))
--             (nhds (globalPatch Y t ω))
--           ∧ ∀ i : Fin n, ∃ ℓ : ℝ,
--               Filter.Tendsto (fun s => globalPatch Y s ω i) (nhdsWithin t (Set.Iio t)) (nhds ℓ)
--   ```
--
--   **Module navigation**
--
--   Module: [`LevyStochCalc/Ito/PicardGlobal`](https://prove2.me/theorems/c943d813-0c09-4024-8228-fab73533b083).
--
--   Previous: [`ae_all_windows_agree`](https://prove2.me/theorems/28b35a3b-dd08-4022-854c-84cd03274ea9) · Next: [`solvesOn_globalPatch`](https://prove2.me/theorems/2037a307-1801-4e9b-8f73-f67d1076a421).
--
--   [Source excerpt, lines 202–213](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Ito/PicardGlobal.lean#L202-L213) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Ito/PicardGlobal.lean#L200-L246 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Ito.PicardGlobal`, declaration `LevyStochCalc.Ito.Picard.cadlag_globalPatch`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

import Definitions.Def_KLSModular_LevyStochCalc_Ito_PicardGlobal

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Ito/PicardGlobal.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory LevyStochCalc.Probability
universe u v
variable {Ω : Type u} [MeasurableSpace Ω] {E : Type v} [MeasurableSpace E]
variable {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P] {n d : ℕ}
variable {ν : MeasureTheory.Measure E} [MeasureTheory.SigmaFinite ν]
variable (W : LevyStochCalc.Brownian.Multidim.MultidimBrownianMotion P d)
variable (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
variable (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›)
omit [MeasurableSpace E] [SigmaFinite ν] [IsProbabilityMeasure P]

theorem LevyStochCalc.Ito.Picard.cadlag_globalPatch_readable {Y : ℕ → ℝ → Ω → (Fin n → ℝ)}
    (hagree : ∀ᵐ ω ∂P, ∀ k : ℕ, ∀ t ∈ Set.Icc (0 : ℝ) ((k : ℝ) + 1),
      globalPatch Y t ω = Y k t ω)
    (hYcad : ∀ k, ∀ᵐ ω ∂P, ∀ t : ℝ,
      Filter.Tendsto (fun s => Y k s ω) (nhdsWithin t (Set.Ioi t)) (nhds (Y k t ω))
        ∧ ∀ i : Fin n, ∃ ℓ : ℝ,
            Filter.Tendsto (fun s => Y k s ω i) (nhdsWithin t (Set.Iio t)) (nhds ℓ)) :
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t →
      Filter.Tendsto (fun s => globalPatch Y s ω) (nhdsWithin t (Set.Ioi t))
          (nhds (globalPatch Y t ω))
        ∧ ∀ i : Fin n, ∃ ℓ : ℝ,
            Filter.Tendsto (fun s => globalPatch Y s ω i) (nhdsWithin t (Set.Iio t)) (nhds ℓ) := by sorry
