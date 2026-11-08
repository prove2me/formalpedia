-- Prove2me | Theorems.Thm_GraphonCheeger_proposition_4_27
-- name    : GraphonCheeger.proposition_4_27
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T05:00:40.113491+00:00
-- url     : https://prove2.me/theorems/0c836cc9-999d-4c7d-a971-6dd8da6a786a
-- title:
--   Proposition 4.27: $|h(W_1)-h(W_2)|\le\frac{4}{c^2}\,\delta_\square(W_1,W_2)$
-- statement:
--   Let $W_1$ and $W_2$ be graphons on possibly different probability spaces with $k_{W_1},k_{W_2}\ge c>0$ almost everywhere. Then
--
--   $$|h(W_1)-h(W_2)|\le\frac{4}{c^2}\,\delta_\square(W_1,W_2).$$
--
--   On graphons with degrees bounded away from $0$ the Cheeger constant is therefore Lipschitz in the cut distance, with an explicit constant.
--
--   Differences from the source:
--   - encoding: the infimum in $\delta_\square$ over all probability spaces → over probability spaces in the universe `Type (max u v)` of the two graphons' spaces; reason: every common space pushes forward to a coupling on $\Omega_1\times\Omega_2$, which lies in that universe and has no larger cut norm, so the value is the same.
-- source:
--   Janson, Lo, McDiarmid, Skeja, Skerman, Graphon Colourings and Limits of Graph Partitions, arXiv:2610.38599 (held version, sha256 3d198813…), Proposition 4.27, (4.129), pp.47–48

import Mathlib
import Definitions.Def_GraphonCheeger_cutDist
import Definitions.Def_GraphonCheeger_cheegerW
import Definitions.Def_GraphonCheeger_InWc

open MeasureTheory

namespace GraphonCheeger

/-- Proposition 4.27, pp.47–48 (Janson, Lo, McDiarmid, Skeja, Skerman, *Graphon Colourings and Limits of Graph Partitions*,
arXiv:2610.38599 (held version, sha256 3d198813…)): let `W₁, W₂` be graphons on possibly different probability
spaces with `k_{W₁}, k_{W₂} ≥ c > 0` a.e. Then `|h(W₁) − h(W₂)| ≤ (4/c²) δ_□(W₁, W₂)` (4.129). -/
theorem proposition_4_27 {Ω₁ : Type*} {Ω₂ : Type*} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂]
    (μ₁ : Measure Ω₁) [IsProbabilityMeasure μ₁] (μ₂ : Measure Ω₂) [IsProbabilityMeasure μ₂]
    (W₁ : Ω₁ → Ω₁ → ℝ) (W₂ : Ω₂ → Ω₂ → ℝ) (hW₁ : IsGraphon W₁) (hW₂ : IsGraphon W₂)
    (c : ℝ) (hc : 0 < c) (hk₁ : InWc μ₁ W₁ c) (hk₂ : InWc μ₂ W₂ c) :
    |cheegerW μ₁ W₁ - cheegerW μ₂ W₂| ≤ 4 / c ^ 2 * cutDist μ₁ W₁ μ₂ W₂ := by sorry

end GraphonCheeger
