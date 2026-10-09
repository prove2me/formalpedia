-- Prove2me | Theorems.Thm_GraphonGames_Stability_lemma_3_7_best_response_lipschitz
-- name    : GraphonGames.Stability.lemma_3_7_best_response_lipschitz
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T17:45:30.857496+00:00
-- url     : https://prove2.me/theorems/d15c5288-19ce-4d45-a1b7-85ba5459e1be
-- title:
--   Lemma 3.7 — Lipschitz best response
-- statement:
--   Let $J(a,z)$ satisfy Assumption 4: it is continuously differentiable and uniformly $\ell_c$-strongly convex in $a$, and its action derivative is $\ell_J$-Lipschitz in $z$. For any $z^1,z^2\in L^2(I)$, let $Bz$ be the profile of pointwise minimizers of $J(\cdot,z(x))$. Then
--
--   $$
--   \|Bz^1-Bz^2\|_{L^2(I)}\leq\frac{\ell_J}{\ell_c}\|z^1-z^2\|_{L^2(I)}.
--   $$
--
--   This controls how a change in the aggregate changes each player's best response.
--
--   **Formalization Note** The choice of a minimizer is encoded by classical choice; Assumption 4 supplies its existence and uniqueness. The norm inequality is in extended nonnegative reals, so an infinite left side cannot become zero under conversion.
-- source:
--   Carmona, Cooney, Graves & Laurière, Stochastic Graphon Games: I. The Static Case, arXiv:1911.10664v1, p. 11, Lemma 3.7

import Mathlib
import Definitions.Def_GraphonGames_Stability_Setting

open MeasureTheory
open scoped ENNReal

namespace GraphonGames.Stability

theorem lemma_3_7_best_response_lipschitz
    (J : ℝ → ℝ → ℝ) (ℓc ℓJ : ℝ) (h4 : GraphonGames.Existence.Asm4 J ℓc ℓJ)
    (z1 z2 : I → ℝ) (hz1 : MemLp z1 2 volume)
    (hz2 : MemLp z2 2 volume) :
    eLpNorm (bestResponse J z1 - bestResponse J z2) 2 volume ≤
      ENNReal.ofReal (ℓJ / ℓc) * eLpNorm (z1 - z2) 2 volume := by sorry

end GraphonGames.Stability
