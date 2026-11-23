-- Prove2me | Theorems.Thm_NoHair_kerr_same_chart_inner_outer_reference_horizons
-- name    : NoHair.kerr_same_chart_inner_outer_reference_horizons
-- status  : Proved
-- author  : @Igor Valuev
-- created : 2026-11-23T07:36:41.017917+00:00
-- url     : https://prove2.me/theorems/db09267e-a47d-41f7-9c59-151d45629c4d
-- title:
--   Changing only the cutoff of one Kerr chart selects the inner or outer horizon
-- statement:
--   Consider ingoing vacuum Kerr with $m=5/2$ and $a=2$, with its canonical time orientation and stationary time translations. One and the same asymptotically flat chart, with the same bounds on the metric and electromagnetic field, gives two reference regions by changing the coordinate cutoff from $1$ to $5$. Their images are $E_1=\{r>1\}$ and $E_5=\{r>5\}$, where $r$ is the Kerr radial coordinate. For the domain of outer communications and the future event horizon defined relative to each end one obtains
--   $$
--   D(E_1)=\{r>1\},\qquad H^+(E_1)=\{r=1\},\qquad
--   D(E_5)=\{r>4\},\qquad H^+(E_5)=\{r=4\}.
--   $$
--   The stationary field is timelike throughout $E_5$, and $D(E_5)$ is isometric as a metric and field to the standard Kerr exterior with the same parameters.
-- source:
--   P. Chruściel and J. Lopes Costa, On uniqueness of stationary vacuum black holes, Section 2.2, p. 7, equations (2.9)–(2.10), https://arxiv.org/abs/0806.0016 . For the explicit Kerr metric, horizons and ergosurface see M. Visser, The Kerr spacetime: A brief introduction, Sections 9–10, https://arxiv.org/abs/0706.0622 .

import Definitions.Def_NoHair_kerrNewmanTimeDirection

open NoHair Set
open scoped ContDiff Manifold

theorem NoHair.kerr_same_chart_inner_outer_reference_horizons : 
    let g := kerrNewmanMetricField (5/2) 2 0
    let F := kerrNewmanFieldField 2 0
    let T := kerrNewmanTimeDirection (5/2) 2 0
    ∃ (φ : ℝ → kerrNewmanSpacetime 2 → kerrNewmanSpacetime 2)
      (E₁ E₅ : AsymptoticallyFlatEnd g F φ),
      IsSymmetryFlow g F φ ∧ (∀ s x, (φ s x).val = x.val + s • coordBasis 0) ∧
      E₁.ψ = E₅.ψ ∧ E₁.C = E₅.C ∧ E₁.R = 1 ∧ E₅.R = 5 ∧
      E₁.region = {x : kerrNewmanSpacetime 2 | 1 < ksRadius 2 x.val} ∧
      E₅.region = {x : kerrNewmanSpacetime 2 | 5 < ksRadius 2 x.val} ∧
      (∀ x ∈ E₅.region, g x (flowGenerator φ x) (flowGenerator φ x) < 0) ∧
      domainOfOuterCommunications g T E₁.region =
        {x : kerrNewmanSpacetime 2 | 1 < ksRadius 2 x.val} ∧
      futureEventHorizon g T E₁.region =
        {x : kerrNewmanSpacetime 2 | ksRadius 2 x.val = 1} ∧
      domainOfOuterCommunications g T E₅.region =
        {x : kerrNewmanSpacetime 2 | 4 < ksRadius 2 x.val} ∧
      futureEventHorizon g T E₅.region =
        {x : kerrNewmanSpacetime 2 | ksRadius 2 x.val = 4} ∧
      IsKerrNewmanDOC g F (domainOfOuterCommunications g T E₅.region) (5/2) 2 0 := by
  sorry
