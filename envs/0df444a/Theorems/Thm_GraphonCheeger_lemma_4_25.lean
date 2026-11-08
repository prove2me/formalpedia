-- Prove2me | Theorems.Thm_GraphonCheeger_lemma_4_25
-- name    : GraphonCheeger.lemma_4_25
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T04:59:50.973828+00:00
-- url     : https://prove2.me/theorems/f5381786-c018-46ab-a70f-6e1d82daa1b4
-- title:
--   Lemma 4.25: near-optimal colourings have denominator $D(W,\psi)\ge c^2/2$
-- statement:
--   Let $W$ be a graphon on a probability space with $k_W\ge c>0$ almost everywhere.
--
--   1. Every measurable mixed colouring $\Psi=(\psi,1-\psi)$ with $D(W,\psi)>0$ and $H(W,\Psi)\le\frac12$ satisfies
--   $$D(W,\psi)\ge\frac{c^2}{2}.$$
--   2. For every $\eta>0$ there is a mixed colouring $\Psi=(\psi,1-\psi)$ with $D(W,\psi)\ge c^2/2$ and
--   $$H(W,\Psi)\le h(W)+\eta .$$
--
--   A uniform lower bound on the denominators of near-optimal colourings is what turns the cut-norm continuity of $C$ and $D$ into continuity of $h$.
--
--   Differences from the source: none.
-- source:
--   Janson, Lo, McDiarmid, Skeja, Skerman, Graphon Colourings and Limits of Graph Partitions, arXiv:2610.38599 (held version, sha256 3d198813…), Lemma 4.25, (4.109)–(4.110), p.46

import Mathlib
import Definitions.Def_GraphonCheeger_cheegerW
import Definitions.Def_GraphonCheeger_InWc

open MeasureTheory

namespace GraphonCheeger

/-- Lemma 4.25, p.46 (Janson, Lo, McDiarmid, Skeja, Skerman, *Graphon Colourings and Limits of Graph Partitions*,
arXiv:2610.38599 (held version, sha256 3d198813…)): let `W` be a graphon with `k_W ≥ c > 0` a.e. Every measurable mixed
colouring `Ψ = (ψ, 1 − ψ)` with `D(W, ψ) > 0` and `H(W, Ψ) ≤ 1/2` satisfies `D(W, ψ) ≥ c²/2`
(4.109); and for every `η > 0` there is a colouring with (4.109) and `H(W, Ψ) ≤ h(W) + η`
(4.110). -/
theorem lemma_4_25 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (W : Ω → Ω → ℝ) (hW : IsGraphon W) (c : ℝ) (hc : 0 < c) (hk : InWc μ W c) :
    (∀ ψ : Ω → ℝ, IsColouring ψ → 0 < denom μ W ψ → ratio μ W ψ ≤ 1 / 2 →
        c ^ 2 / 2 ≤ denom μ W ψ) ∧
    (∀ η : ℝ, 0 < η → ∃ ψ : Ω → ℝ, IsColouring ψ ∧ c ^ 2 / 2 ≤ denom μ W ψ ∧
        ratio μ W ψ ≤ cheegerW μ W + η) := by sorry

end GraphonCheeger
