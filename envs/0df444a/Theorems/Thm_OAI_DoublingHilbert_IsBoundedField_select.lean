-- Prove2me | Theorems.Thm_OAI_DoublingHilbert_IsBoundedField_select
-- name    : OAI.DoublingHilbert.IsBoundedField.select
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-14T22:21:18.491143+00:00
-- url     : https://prove2.me/theorems/26a7d0b0-f4b9-4c09-850e-7936e5943fe1
-- title:
--   A measurable selection from finitely many bounded measurable fields is bounded and measurable
-- statement:
--   Let $X$ be a measurable space and $E$ a normed abelian group. Call $g:X\to E$ a bounded field if $g$ is strongly measurable and there is a real $M$ with $\|g(x)\|\le M$ for all $x\in X$.
--
--   **Theorem.** Let $I$ be a finite index set carrying a $\sigma$-algebra in which all singletons are measurable, let $(g_i)_{i\in I}$ be bounded fields $g_i:X\to E$, and let $\sigma:X\to I$ be measurable. Then the selected field
--   $$
--   x\longmapsto g_{\sigma(x)}(x)
--   $$
--   is again a bounded field.
--
--   The lemma is used to show that derivative columns chosen according to the color of the strip containing a point (one of finitely many Lipschitz sheets, selected by a measurable strip-color rule) can be integrated over rectangles and handled by Fubini's theorem.
--
--   **Formalization Note** Bounded fields are `IsBoundedField g`, meaning `StronglyMeasurable g` together with a uniform norm bound; the index type has instances `Fintype I`, `MeasurableSpace I` and `MeasurableSingletonClass I`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/DoublingHilbert/Rectangles.lean#L167-L184

import Mathlib
import Definitions.Def_DoublingHilbert
import Definitions.Def_OAI_Geometry_DoublingHilbert_Construction
import Definitions.Def_OAI_Geometry_DoublingHilbert_Derivatives
import Definitions.Def_OAI_Geometry_DoublingHilbert_Integration
import Definitions.Def_OAI_Geometry_DoublingHilbert_Rectangles

open OAI OAI.DoublingHilbert OAI.DoublingHilbert.IsBoundedField
open MeasureTheory Set Filter
open scoped BigOperators Topology
open MeasureTheory Set Filter
open scoped Topology
open MeasureTheory Set Filter
open scoped Topology
variable {X Y I E : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  [NormedAddCommGroup E]

theorem OAI.DoublingHilbert.IsBoundedField.select [Fintype I] [MeasurableSpace I] [MeasurableSingletonClass I]
    {g : I → X → E} (hg : ∀ i, IsBoundedField (g i))
    {σ : X → I} (hσ : Measurable σ) : IsBoundedField (fun p => g (σ p) p) := by sorry
