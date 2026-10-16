-- Prove2me | Theorems.Thm_OAI_Problem310_CenterExposure_map_fresh_restrict_center_atom
-- name    : OAI.Problem310.CenterExposure.map_fresh_restrict_center_atom
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T04:09:27.180162+00:00
-- url     : https://prove2.me/theorems/b3f230ca-711f-4956-a1fd-26ed7f5eec83
-- title:
--   Fixing center entries of an i.i.d. table leaves the fresh entries i.i.d., scaled by the atom's mass
-- statement:
--   Let $C$, $I$ and $K$ be finite sets, and let $B$ be a countable measurable space in which every singleton is measurable. Let $\nu$ be a probability measure on $B$ and equip $B^K$ with the product measure $P=\nu^{\otimes K}$, so that the entries of a random table $\omega\in B^K$ are independent with law $\nu$. Let $\mathrm{center}:C\to K$ and $\mathrm{fresh}:I\to K$ be maps whose combination $C\sqcup I\to K$ is injective; that is, both maps are injective and $\mathrm{center}(c)\ne\mathrm{fresh}(i)$ for all $c\in C$ and $i\in I$. Fix values $v=(v_c)_{c\in C}\in B^C$, let
--   $$A=\bigl\{\omega\in B^K:\ \omega_{\mathrm{center}(c)}=v_c\ \text{for all } c\in C\bigr\}$$
--   be the corresponding center atom, and let $\pi:B^K\to B^I$, $\pi(\omega)=(\omega_{\mathrm{fresh}(i)})_{i\in I}$, read the fresh entries. Then the image under $\pi$ of the restricted measure $P|_A$ (the measure $E\mapsto P(A\cap E)$) is
--
--   $$\pi_{*}\bigl(P|_A\bigr)=\Bigl(\prod_{c\in C}\nu(\{v_c\})\Bigr)\,\nu^{\otimes I}.$$
--
--   Equivalently, $P\bigl(A\cap\pi^{-1}(E)\bigr)=\bigl(\prod_{c\in C}\nu(\{v_c\})\bigr)\,\nu^{\otimes I}(E)$ for every measurable $E\subseteq B^I$, and taking $E=B^I$ shows that the prefactor is $P(A)$. Thus prescribing the values of the exposed center entries does not change the joint law of the fresh entries: they stay independent with law $\nu$, and the only effect is the scalar factor $P(A)$. This unnormalized form avoids conditional probabilities and applies to arbitrary events and moments of the whole fresh vector, not only to cylinder events.
--
--   **Formalization Note** The combined map is `Sum.elim center fresh`, the left side is `Measure.map` of `Measure.restrict`, and the right side is a scalar multiple, by an extended nonnegative real, of `Measure.pi (fun _ : I => ν)`. Countability of $B$ and measurability of singletons are the hypotheses `[Countable B]` and `[MeasurableSingletonClass B]`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MeasureTheory/DyadicAvoidance/CenterExposure.lean#L70-L100

import Mathlib
import Definitions.Def_DyadicAvoidance
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_PeriodicBasic

open OAI OAI.Problem310
universe u_C u_I u_K u_B
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

theorem OAI.Problem310.CenterExposure.map_fresh_restrict_center_atom
    {C : Type u_C} {I : Type u_I} {K : Type u_K} {B : Type u_B} [Fintype C] [Fintype I] [Fintype K] [Countable B]
    [MeasurableSpace B] [MeasurableSingletonClass B]
    (ν : Measure B) [IsProbabilityMeasure ν]
    (center : C → K) (fresh : I → K)
    (hinj : Function.Injective (Sum.elim center fresh)) (value : C → B) :
    Measure.map (fun ω : K → B => fun i => ω (fresh i))
      ((Measure.pi (fun _ : K => ν)).restrict
        {ω | ∀ c, ω (center c) = value c}) =
      (∏ c, ν {value c}) • Measure.pi (fun _ : I => ν) := by sorry
