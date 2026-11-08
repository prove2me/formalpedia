-- Prove2me | Theorems.Thm_GraphonCheeger_lemma_4_22
-- name    : GraphonCheeger.lemma_4_22
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T04:58:18.617178+00:00
-- url     : https://prove2.me/theorems/289a4b9b-7533-4e0f-a1d1-7834577ab583
-- title:
--   Lemma 4.22: $0\le h(W)\le 1/2$
-- statement:
--   For every graphon $W$ on a probability space with $\rho_W>0$, the mixed Cheeger constant satisfies
--
--   $$0\le h(W)\le\tfrac12 .$$
--
--   The upper bound gives an admissible colouring with ratio at most $1/2$ for every graphon of positive density, which is the starting point of the uniform denominator bound.
--
--   Differences from the source: none.
-- source:
--   Janson, Lo, McDiarmid, Skeja, Skerman, Graphon Colourings and Limits of Graph Partitions, arXiv:2610.38599 (held version, sha256 3d198813…), Lemma 4.22, (4.88), p.44

import Mathlib
import Definitions.Def_GraphonCheeger_cheegerW

open MeasureTheory

namespace GraphonCheeger

/-- Lemma 4.22, p.44 (Janson, Lo, McDiarmid, Skeja, Skerman, *Graphon Colourings and Limits of Graph Partitions*,
arXiv:2610.38599 (held version, sha256 3d198813…)): for every graphon `W` with `ρ_W > 0`, `0 ≤ h(W) ≤ 1/2` (4.88),
where `h(W)` is the mixed Cheeger constant. -/
theorem lemma_4_22 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (W : Ω → Ω → ℝ) (hW : IsGraphon W) (hρ : 0 < density μ W) :
    0 ≤ cheegerW μ W ∧ cheegerW μ W ≤ 1 / 2 := by sorry

end GraphonCheeger
