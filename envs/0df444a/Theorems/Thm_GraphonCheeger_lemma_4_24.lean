-- Prove2me | Theorems.Thm_GraphonCheeger_lemma_4_24
-- name    : GraphonCheeger.lemma_4_24
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T04:55:55.995102+00:00
-- url     : https://prove2.me/theorems/b402ee74-d654-48cf-a8a8-e19df6be7e02
-- title:
--   Lemma 4.24: $C$, $D$ and $m$ are $1$-Lipschitz in the cut norm
-- statement:
--   Let $W_1,W_2$ be graphons on the same probability space $(\Omega,\mathcal F,\mu)$. Then for every measurable $\psi:\Omega\to[0,1]$,
--
--   $$|C(W_1,\psi)-C(W_2,\psi)|\le\|W_1-W_2\|_\square,$$
--
--   $$|D(W_1,\psi)-D(W_2,\psi)|\le\|W_1-W_2\|_\square,$$
--
--   $$|m(W_1,\psi)-m(W_2,\psi)|\le\|W_1-W_2\|_\square .$$
--
--   These bounds are the cut-norm continuity of the numerator and denominator of the coloured Cheeger ratio, uniformly in the colouring.
--
--   Differences from the source: none.
-- source:
--   Janson, Lo, McDiarmid, Skeja, Skerman, Graphon Colourings and Limits of Graph Partitions, arXiv:2610.38599 (held version, sha256 3d198813…), Lemma 4.24, (4.100)–(4.102), p.45

import Mathlib
import Definitions.Def_GraphonCheeger_cutDist
import Definitions.Def_GraphonCheeger_cheegerW

open MeasureTheory

namespace GraphonCheeger

/-- Lemma 4.24, p.45 (Janson, Lo, McDiarmid, Skeja, Skerman, *Graphon Colourings and Limits of Graph Partitions*,
arXiv:2610.38599 (held version, sha256 3d198813…)): for graphons `W₁, W₂` on the same probability space and every
measurable `ψ : Ω → [0, 1]`, each of `C(·, ψ)`, `D(·, ψ)`, `m(·, ψ)` changes by at most
`‖W₁ − W₂‖_□` ((4.100)–(4.102)). -/
theorem lemma_4_24 {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (W₁ W₂ : Ω → Ω → ℝ) (hW₁ : IsGraphon W₁) (hW₂ : IsGraphon W₂)
    (ψ : Ω → ℝ) (hψ : IsColouring ψ) :
    |cutVal μ W₁ ψ - cutVal μ W₂ ψ| ≤ cutNorm μ (fun x y => W₁ x y - W₂ x y) ∧
    |denom μ W₁ ψ - denom μ W₂ ψ| ≤ cutNorm μ (fun x y => W₁ x y - W₂ x y) ∧
    |mass μ W₁ ψ - mass μ W₂ ψ| ≤ cutNorm μ (fun x y => W₁ x y - W₂ x y) := by sorry

end GraphonCheeger
