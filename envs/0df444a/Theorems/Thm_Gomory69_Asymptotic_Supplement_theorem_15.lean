-- Prove2me | Theorems.Thm_Gomory69_Asymptotic_Supplement_theorem_15
-- name    : Gomory69.Asymptotic.Supplement.theorem_15
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T01:27:03.989913+00:00
-- url     : https://prove2.me/theorems/988b6c5f-439f-4fb9-b94a-e1df9834d2b3
-- title:
--   THEOREM 15 — Subvectors of vertices (corrected: exact nonzero criterion)
-- statement:
--   Let $G$ be a finite Abelian group, $t$ a vertex of the published master polyhedron $P(G,g_0)$, and $s\in\mathbb N^{G^+}$ with $s(g)\le t(g)$. Set $h=\sum_{g\in G^+}s(g)g$. Then
--   $$s\in\operatorname{ext}P(G,h)\quad\Longleftrightarrow\quad s\ne0.$$
--   Every nonzero integer subvector has the vertex property claimed in the paper. The zero subvector is never even a point of $P(G,0)$ under the p. 474 convention. For example, $t(1)=1$ in $G=\mathbb Z/2$ is a vertex at target $1$, whereas its zero subvector is not a vertex at target $0$.
--
--   This gives the full-domain corrected subvector criterion, including an explicit answer at the excluded empty path.
--
--   Differences from the source:
--   - correction: every nonnegative integer subvector, including zero, is a vertex for its target → vertex membership is equivalent to the subvector being nonzero; reason: the p. 474 footnote excludes the zero solution from P(G,0); the original conclusion fails for s=0, while the p. 479 subpath argument applies to every nonzero subvector
--   - reading: the sum s(g)g is a group sum and paths have integer multiplicities → s is Nat-valued and t is a real extreme point; reason: pp. 472 and 479 use integer path subvectors; integrality of t follows from being a vertex of this integer hull and is not assumed as an extra condition
-- source:
--   Gomory, Some polyhedra related to combinatorial problems, Linear Algebra Appl. 2 (1969), DOI 10.1016/0024-3795(69)90017-2, p. 479, THEOREM 15

import Mathlib
import Definitions.Def_Gomory69_Lifting_GroupPolyhedron

namespace Gomory69.Asymptotic.Supplement

/-- The source subvector conclusion holds exactly for the nonzero subvectors, because
its zero-target master convention excludes the zero vector. -/
theorem theorem_15 {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (g₀ : G) (t : Gomory69.Lifting.Plus G → ℝ)
    (ht : t ∈ Set.extremePoints ℝ (Gomory69.Lifting.P G g₀))
    (s : Gomory69.Lifting.Plus G → ℕ) (hst : ∀ g, (s g : ℝ) ≤ t g) :
    Gomory69.Lifting.castVec s ∈ Set.extremePoints ℝ
      (Gomory69.Lifting.P G (∑ g : Gomory69.Lifting.Plus G, s g • (g : G))) ↔
      s ≠ 0 := by sorry

end Gomory69.Asymptotic.Supplement
