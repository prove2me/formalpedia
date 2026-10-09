-- Prove2me | Theorems.Thm_GraphonGames_Stability_lemma_3_19_aggregate_graphon_stability
-- name    : GraphonGames.Stability.lemma_3_19_aggregate_graphon_stability
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T17:45:37.092468+00:00
-- url     : https://prove2.me/theorems/187bb874-2ff0-45f7-abc5-e2bf44a49a1d
-- title:
--   Lemma 3.19 — aggregate stability under a change of graphon
-- statement:
--   Under Assumptions 1, 4, and 5, let $w,w'$ be graphons with operators $W,W'$ satisfying $\sqrt{c_z}\|W\|<1$ and $\sqrt{c_z}\|W'\|<1$. For a fixed $L^2$ strategy profile $\alpha$, let $Z\alpha$ and $Z'\alpha$ be its aggregates under $w$ and $w'$. Then
--
--   $$
--   \|Z\alpha-Z'\alpha\|_{L^2(I)}\leq
--   \frac{c_0}{1-\sqrt{c_z}\|W\|}\|W-W'\|.
--   $$
--
--   This isolates the effect of changing the interaction kernel while keeping actions fixed.
--
--   **Formalization Note** The right side uses the operator norm of the difference kernel. Assumption 4 is retained as printed, although this estimate does not use it in the paper's proof.
-- source:
--   Carmona, Cooney, Graves & Laurière, Stochastic Graphon Games: I. The Static Case, arXiv:1911.10664v1, p. 17, Lemma 3.19

import Mathlib
import Definitions.Def_GraphonGames_Stability_Setting

open MeasureTheory
open scoped ENNReal

namespace GraphonGames.Stability

theorem lemma_3_19_aggregate_graphon_stability
    (b : ℝ → ℝ → ℝ) (f : ℝ → ℝ → ℝ → ℝ)
    (μ0 : Measure ℝ) (cα cz ℓc ℓJ c0 : ℝ)
    (h1 : GraphonGames.Existence.Asm1 b μ0 cα cz)
    (h4 : GraphonGames.Existence.Asm4 (GraphonGames.Existence.cost b f μ0) ℓc ℓJ)
    (h5 : GraphonGames.Existence.Asm5 b c0)
    (w w' : I → I → ℝ) (hw : IsGraphon w) (hw' : IsGraphon w')
    (hW : Real.sqrt cz * (opNorm w).toReal < 1)
    (hW' : Real.sqrt cz * (opNorm w').toReal < 1)
    (α : I → ℝ) (hα : MemLp α 2 volume)
    (z z' : I → ℝ) (hz : IsAggregate w b α z)
    (hz' : IsAggregate w' b α z') :
    eLpNorm (z - z') 2 volume ≤
      ENNReal.ofReal
        (c0 / (1 - Real.sqrt cz * (opNorm w).toReal)) *
        opNorm (w - w') := by sorry

end GraphonGames.Stability
