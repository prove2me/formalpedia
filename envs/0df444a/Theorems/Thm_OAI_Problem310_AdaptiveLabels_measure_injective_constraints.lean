-- Prove2me | Theorems.Thm_OAI_Problem310_AdaptiveLabels_measure_injective_constraints
-- name    : OAI.Problem310.AdaptiveLabels.measure_injective_constraints
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T04:08:28.923593+00:00
-- url     : https://prove2.me/theorems/ff1a77d2-a6e1-4774-a920-a8c48870ed82
-- title:
--   Constraints on distinct coordinates of an i.i.d. table have product probability
-- statement:
--   Let $I$ and $K$ be finite sets, let $(B,\mathcal{B})$ be a measurable space and let $\nu$ be a probability measure on $B$. Equip $B^K$ with the product $\sigma$-algebra and the product measure $\nu^{\otimes K}$, so that the entries $\omega_k$ ($k\in K$) of a random table $\omega\in B^K$ are independent with common law $\nu$. Let $\mathrm{addr}:I\to K$ be an injective map and let $s_i\in\mathcal{B}$ be a measurable set for each $i\in I$. Then
--
--   $$\nu^{\otimes K}\Bigl(\bigl\{\omega\in B^K:\ \omega_{\mathrm{addr}(i)}\in s_i\ \text{for all } i\in I\bigr\}\Bigr)=\prod_{i\in I}\nu(s_i).$$
--
--   In words, tests that read pairwise distinct addresses of a table of i.i.d. labels are independent, and the entries of the table that are not read play no role. This is the basic factorization used whenever finitely many tests are evaluated on a random label table; it is the starting point for the versions with adaptively chosen addresses and with conditioning on exposed entries.
--
--   **Formalization Note** The product measure is `Measure.pi (fun _ : K => ν)` on functions `K → B`, both sides are extended nonnegative reals, and the index sets are `Fintype`s.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MeasureTheory/DyadicAvoidance/AdaptiveLabels.lean#L12-L34

import Mathlib
import Definitions.Def_DyadicAvoidance
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_PeriodicBasic

open OAI OAI.Problem310
universe u_I u_K u_B u_A
open MeasureTheory ProbabilityTheory
open scoped BigOperators

theorem OAI.Problem310.AdaptiveLabels.measure_injective_constraints
    {I : Type u_I} {K : Type u_K} {B : Type u_B} [Fintype I] [Fintype K] [MeasurableSpace B]
    (ν : Measure B) [IsProbabilityMeasure ν]
    (addr : I → K) (hinj : Function.Injective addr)
    (s : I → Set B) (hs : ∀ i, MeasurableSet (s i)) :
    (Measure.pi (fun _ : K => ν)) {ω | ∀ i, ω (addr i) ∈ s i} =
      ∏ i, ν (s i) := by sorry
