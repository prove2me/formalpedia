-- Prove2me | Theorems.Thm_Garrido_isParadoxical_sphere_two_and_isParadoxical_sphere
-- name    : Garrido.isParadoxical_sphere_two_and_isParadoxical_sphere
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-24T14:02:32.712204+00:00
-- url     : https://prove2.me/theorems/74439c98-15a2-482b-9f92-489fa8fbde4e
-- title:
--   Corollary 1.9 — the spheres Sⁿ, n ≥ 2, are paradoxical under rotations
-- statement:
--   The $2$-sphere is $SO(3,\mathbb{R})$-paradoxical, and more generally, for every
--   $n \ge 2$, the $n$-sphere is $SO(n+1,\mathbb{R})$-paradoxical:
--
--   $$S^2 \text{ is } SO(3,\mathbb{R})\text{-paradoxical}, \qquad S^n \text{ is } SO(n+1,\mathbb{R})\text{-paradoxical} \ (n \ge 2).$$
--
--   The second clause contains the first; both are stated because the source states both. It rules
--   out a rotation-invariant finitely additive probability measure on all subsets of $S^n$.
--
--   **Formalization Note.** $S^n$ is `Sphere n` and $SO(n+1,\mathbb{R})$ acts by matrix-vector
--   multiplication; paradoxicality is the imported `IsParadoxical` for the whole sphere.
-- source:
--   A. Garrido, "An introduction to amenable groups", lecture notes, Oxford Advanced Class in Algebra, Michaelmas 2013 (PDF, Feb 2015), p. 3, Corollary 1.9 (Banach–Tarski); https://web.archive.org/web/20260805000803/https://www.math.uni-duesseldorf.de/~garrido/amenable.pdf

import Mathlib
import Definitions.Def_Garrido_BanachTarski
import Definitions.Def_Garrido_Equidecomposability

namespace Garrido

theorem isParadoxical_sphere_two_and_isParadoxical_sphere :
    IsParadoxical (Matrix.specialOrthogonalGroup (Fin 3) ℝ) (Set.univ : Set (Sphere 2)) ∧
      ∀ n : ℕ, 2 ≤ n →
        IsParadoxical (Matrix.specialOrthogonalGroup (Fin (n + 1)) ℝ) (Set.univ : Set (Sphere n)) := by
  sorry

end Garrido
