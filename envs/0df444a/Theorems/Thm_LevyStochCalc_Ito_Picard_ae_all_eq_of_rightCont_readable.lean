-- Prove2me | Theorems.Thm_LevyStochCalc_Ito_Picard_ae_all_eq_of_rightCont_readable
-- name    : LevyStochCalc.Ito.Picard.ae_all_eq_of_rightCont_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:11:19.12999+00:00
-- url     : https://prove2.me/theorems/439cca99-ccce-4335-8a27-57cecb8617ae
-- title:
--   Almost-Everywhere Pathwise Equality from Right Continuity
-- statement:
--   This promotes equality at each fixed time to simultaneous almost-everywhere equality on a time window.
--
--   Let $A,B:\mathbb R\to\Omega\to\mathbb R^n$ and $T\in\mathbb R$. Assume: (1) for almost every $\omega$, $t\mapsto A(t,\omega)$ is right-continuous; (2) for almost every $\omega$, $t\mapsto B(t,\omega)$ is right-continuous; and (3) for every $t\in[0,T]$, $A(t,\omega)=B(t,\omega)$ for almost every $\omega$.
--
--   Then
--
--   $$\forall^{\mathrm{a.e.}}\omega,\ \forall t\in[0,T],\quad A(t,\omega)=B(t,\omega).$$
--
--   No probability or measurability structure beyond that appearing in the type is required. This is a standard separability upgrade using right continuity.
--
--   **Original Lean declaration header**
--
--   Within namespace `LevyStochCalc.Ito.Picard`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem ae_all_eq_of_rightCont {A B : ℝ → Ω → (Fin n → ℝ)} {T : ℝ}
--       (hA : ∀ᵐ ω ∂P, ∀ t : ℝ,
--         Filter.Tendsto (fun s => A s ω) (nhdsWithin t (Set.Ioi t)) (nhds (A t ω)))
--       (hB : ∀ᵐ ω ∂P, ∀ t : ℝ,
--         Filter.Tendsto (fun s => B s ω) (nhdsWithin t (Set.Ioi t)) (nhds (B t ω)))
--       (h : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ᵐ ω ∂P, A t ω = B t ω) :
--       ∀ᵐ ω ∂P, ∀ t ∈ Set.Icc (0 : ℝ) T, A t ω = B t ω
--   ```
--
--   **Module navigation**
--
--   Module: [`LevyStochCalc/Ito/PicardGlobal`](https://prove2.me/theorems/c943d813-0c09-4024-8228-fab73533b083).
--
--   Next: [`progressivelyMeasurable_globalPatch`](https://prove2.me/theorems/d7b4eeb7-145e-4369-9114-1296769d3100).
--
--   [Source excerpt, lines 32–38](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/vendor/LevyStochCalc/LevyStochCalc/Ito/PicardGlobal.lean#L32-L38) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/cgarryZA/LevyStochCalc/blob/984dbf0b790031eac05d56fe5a84b65e15e1e932/LevyStochCalc/Ito/PicardGlobal.lean#L29-L82 (repository human-ai-mathematics/kls-lean, commit 408915f, module `LevyStochCalc.Ito.PicardGlobal`, declaration `LevyStochCalc.Ito.Picard.ae_all_eq_of_rightCont`; the repository is private at upload time). Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (Apache-2.0; upstream copyright notice retained in the Lean text).

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
omit [MeasurableSpace E] [IsProbabilityMeasure P]

theorem LevyStochCalc.Ito.Picard.ae_all_eq_of_rightCont_readable {A B : ℝ → Ω → (Fin n → ℝ)} {T : ℝ}
    (hA : ∀ᵐ ω ∂P, ∀ t : ℝ,
      Filter.Tendsto (fun s => A s ω) (nhdsWithin t (Set.Ioi t)) (nhds (A t ω)))
    (hB : ∀ᵐ ω ∂P, ∀ t : ℝ,
      Filter.Tendsto (fun s => B s ω) (nhdsWithin t (Set.Ioi t)) (nhds (B t ω)))
    (h : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ᵐ ω ∂P, A t ω = B t ω) :
    ∀ᵐ ω ∂P, ∀ t ∈ Set.Icc (0 : ℝ) T, A t ω = B t ω := by sorry
