-- Prove2me | Theorems.Thm_FunctionalInequalities_Poincare_SmoothTest_holds_map_linearIsometryEquiv_iff_readable
-- name    : FunctionalInequalities.Poincare.SmoothTest.holds_map_linearIsometryEquiv_iff_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:18:36.040134+00:00
-- url     : https://prove2.me/theorems/994941b6-460f-44b5-89a4-136cdc8afd35
-- title:
--   Poincaré Inequality Invariance Under Isometries
-- statement:
--   This is the transport equivalence for the fixed-constant smooth-test Poincaré statement.
--
--   Let $E$ and $F$ be complete real inner-product normed spaces equipped with measurable Borel structures. Let $e:E\simeq F$ be a linear isometry equivalence, let $\mu$ be a probability measure on $E$, and let $C\in\mathbb R$. Then
--
--   $$
--   \operatorname{Holds}(e_*\mu,C)
--   \iff
--   \operatorname{Holds}(\mu,C),
--   $$
--
--   where $e_*\mu=\operatorname{Measure.map}(e,\mu)$.
--
--   The declaration records that the repository's smooth-test Poincaré inequality with constant $C$ is unchanged by a linear isometric equivalence of the underlying space.
--
--   **Formalization Note**: `Holds` is the fixed-constant predicate used by the smooth-test Poincaré development. The statement is an iff and does not identify `Holds` with a closed Dirichlet-form domain.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Poincare.SmoothTest`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem holds_map_linearIsometryEquiv_iff {C : ℝ} :
--       Holds (μ.map e) C ↔ Holds μ C
--   ```
--
--   **Module navigation**
--
--   Module: [`Poincare/SmoothTest/Transport`](https://prove2.me/theorems/f97165f6-9a6a-4e3a-aff4-a4bd22cfc6b6).
--
--   Definition modules: [`Poincare/SmoothTest/Basic`](https://prove2.me/theorems/7c7194af-fecd-4f43-8cb7-78130970d14f).
--
--   Supporting theorems: [`admissible_map_linearIsometryEquiv_iff`](https://prove2.me/theorems/efd61af4-c91b-48fd-a2eb-046306bcfae2), [`gradient_comp_projection`](https://prove2.me/theorems/1d27c79a-04ce-4f28-998e-35a7f0d8fec0).
--
--   Previous: [`admissible_map_linearIsometryEquiv_iff`](https://prove2.me/theorems/efd61af4-c91b-48fd-a2eb-046306bcfae2).
--
--   [Source excerpt, lines 189–190](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Poincare/SmoothTest/Transport.lean#L189-L190) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Poincare/SmoothTest/Transport.lean#L187-L209 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Poincare.SmoothTest.Transport`, declaration `FunctionalInequalities.Poincare.SmoothTest.holds_map_linearIsometryEquiv_iff`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Poincare_SmoothTest_Transport

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
variable [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F]
variable (e : E ≃ₗᵢ[ℝ] F) (μ : MeasureTheory.Measure E) [MeasureTheory.IsProbabilityMeasure μ]

theorem FunctionalInequalities.Poincare.SmoothTest.holds_map_linearIsometryEquiv_iff_readable {C : ℝ} :
    Holds (μ.map e) C ↔ Holds μ C := by sorry
