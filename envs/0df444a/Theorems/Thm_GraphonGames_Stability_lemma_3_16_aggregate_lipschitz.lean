-- Prove2me | Theorems.Thm_GraphonGames_Stability_lemma_3_16_aggregate_lipschitz
-- name    : GraphonGames.Stability.lemma_3_16_aggregate_lipschitz
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T17:45:24.313008+00:00
-- url     : https://prove2.me/theorems/ce76698e-a8b9-4274-8ff1-7c66e28eef33
-- title:
--   Lemma 3.16 (15) — Lipschitz aggregate in the strategy profile
-- statement:
--   Under Assumption 1, let $w$ be a graphon whose operator $W$ satisfies $\sqrt{c_z}\|W\|<1$. For profiles $\alpha^1,\alpha^2\in L^2(I)$ and their aggregates $Z\alpha^1,Z\alpha^2$,
--
--   $$
--   \|Z\alpha^1-Z\alpha^2\|_{L^2(I)}\leq
--   \frac{\sqrt{c_\alpha}\|W\|}{1-\sqrt{c_z}\|W\|}
--   \|\alpha^1-\alpha^2\|_{L^2(I)}.
--   $$
--
--   This is the $L^2$ part of Lemma 3.16 and supplies the aggregate sensitivity used in the equilibrium contraction condition.
--
--   **Formalization Note** Aggregates are explicit witnesses of equation (6), rather than values of a total choice function. The pointwise bound (16) is outside this milestone.
-- source:
--   Carmona, Cooney, Graves & Laurière, Stochastic Graphon Games: I. The Static Case, arXiv:1911.10664v1, p. 15, Lemma 3.16, display (15)

import Mathlib
import Definitions.Def_GraphonGames_Stability_Setting

open MeasureTheory
open scoped ENNReal

namespace GraphonGames.Stability

theorem lemma_3_16_aggregate_lipschitz
    (b : ℝ → ℝ → ℝ) (μ0 : Measure ℝ) (cα cz : ℝ)
    (h1 : GraphonGames.Existence.Asm1 b μ0 cα cz)
    (w : I → I → ℝ) (hw : IsGraphon w)
    (hW : Real.sqrt cz * (opNorm w).toReal < 1)
    (α1 α2 : I → ℝ) (hα1 : MemLp α1 2 volume)
    (hα2 : MemLp α2 2 volume)
    (z1 z2 : I → ℝ) (hz1 : IsAggregate w b α1 z1)
    (hz2 : IsAggregate w b α2 z2) :
    eLpNorm (z1 - z2) 2 volume ≤
      ENNReal.ofReal
        (Real.sqrt cα * (opNorm w).toReal /
          (1 - Real.sqrt cz * (opNorm w).toReal)) *
        eLpNorm (α1 - α2) 2 volume := by sorry

end GraphonGames.Stability
