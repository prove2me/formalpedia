-- Prove2me | Theorems.Thm_GraphonGames_Existence_lemma_3_7_best_response_lipschitz
-- name    : GraphonGames.Existence.lemma_3_7_best_response_lipschitz
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T16:55:33.052933+00:00
-- url     : https://prove2.me/theorems/c8606670-90c7-455f-ba30-b30c662b6251
-- title:
--   Lemma 3.7, p. 11 — ‖Bz¹ − Bz²‖_{L²(I)} ≤ (ℓ_J/ℓ_c)‖z¹ − z²‖_{L²(I)}
-- statement:
--   Let $J:\mathbb R\times\mathbb R\to\mathbb R$ satisfy Assumption 4 with constants $\ell_c>0$ and $\ell_J\ge0$, and let $\mathbf B$ be the best-response map, $[\mathbf Bz]_x=\arg\min_{\alpha\in\mathbb R}J(\alpha,z_x)$. For any $z^1,z^2\in L^2(I)$,
--   $$\|\mathbf Bz^1-\mathbf Bz^2\|_{L^2(I)}\le\frac{\ell_J}{\ell_c}\,\|z^1-z^2\|_{L^2(I)}.$$
--
--   The best response is Lipschitz in the aggregate; in the existence proof this gives continuity of $\mathbf B$.
--
--   **Formalization Note.** The lemma is stated for any $J$ satisfying Assumption 4, not only for the cost built from $b,f,\mu_0$, as the paper's hypothesis "Under Assumption 4" allows. Norms are compared in $[0,\infty]$.
-- source:
--   Carmona, Cooney, Graves & Laurière, Stochastic Graphon Games: I. The Static Case, arXiv:1911.10664v1, p. 11, Lemma 3.7

import Mathlib
import Definitions.Def_GraphonGames_Existence_Setting

open MeasureTheory
open scoped ENNReal

namespace GraphonGames.Existence

theorem lemma_3_7_best_response_lipschitz (J : ℝ → ℝ → ℝ) (ℓc ℓJ : ℝ) (h4 : Asm4 J ℓc ℓJ)
    (z1 z2 : I → ℝ) (hz1 : MemLp z1 2 volume) (hz2 : MemLp z2 2 volume) :
    eLpNorm (bestResponse J z1 - bestResponse J z2) 2 volume ≤
      ENNReal.ofReal (ℓJ / ℓc) * eLpNorm (z1 - z2) 2 volume := by sorry

end GraphonGames.Existence
