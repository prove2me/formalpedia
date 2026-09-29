-- Prove2me | Theorems.Thm_Garrido_isParadoxical_closedBall_and_isParadoxical_univ
-- name    : Garrido.isParadoxical_closedBall_and_isParadoxical_univ
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-24T14:06:02.877717+00:00
-- url     : https://prove2.me/theorems/5d1e7197-edc5-4e0b-a04d-279920a03ff7
-- title:
--   Corollary 1.10 — the Banach–Tarski paradox
-- statement:
--   Every closed ball of positive radius in $\mathbb{R}^3$ is paradoxical under the
--   isometry group $E(3)$ of $\mathbb{R}^3$, and so is $\mathbb{R}^3$ itself:
--
--   $$\overline{B}(c, r) \text{ is } E(3)\text{-paradoxical for } r > 0, \qquad \mathbb{R}^3 \text{ is } E(3)\text{-paradoxical}.$$
--
--   This is the Banach–Tarski paradox: a solid ball can be cut into finitely many pieces that
--   isometries reassemble into two copies of itself.
--
--   **Formalization Note.** Paradoxicality is the imported `IsParadoxical`, relative to the ball:
--   the pieces lie in the ball and are moved by isometries of the whole of $\mathbb{R}^3$. The ball
--   is `Metric.closedBall c r`, for any center $c$ and radius $r > 0$; the source's "solid ball" is
--   read as a closed ball of positive radius.
-- source:
--   A. Garrido, "An introduction to amenable groups", lecture notes, Oxford Advanced Class in Algebra, Michaelmas 2013 (PDF, Feb 2015), p. 3, Corollary 1.10 (Banach–Tarski paradox); https://web.archive.org/web/20260805000803/https://www.math.uni-duesseldorf.de/~garrido/amenable.pdf. The result is due to S. Banach and A. Tarski, "Sur la décomposition des ensembles de points en parties respectivement congruentes", Fund. Math. 6 (1924), 244–277; https://doi.org/10.4064/fm-6-1-244-277

import Mathlib
import Definitions.Def_Garrido_BanachTarski
import Definitions.Def_Garrido_Equidecomposability

namespace Garrido

theorem isParadoxical_closedBall_and_isParadoxical_univ :
    (∀ (c : EuclideanSpace ℝ (Fin 3)) (r : ℝ), 0 < r →
        IsParadoxical (EuclideanGroup 3) (Metric.closedBall c r)) ∧
      IsParadoxical (EuclideanGroup 3) (Set.univ : Set (EuclideanSpace ℝ (Fin 3))) := by
  sorry

end Garrido
