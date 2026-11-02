-- Prove2me | Theorems.Thm_Grunbaum2003_exposedFace_finrank_lt_of_ssubset
-- name    : Grunbaum2003.exposedFace_finrank_lt_of_ssubset
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-01T18:01:05.165299+00:00
-- url     : https://prove2.me/theorems/6d6cb5db-52dc-4bc3-8b23-004959fffa16
-- title:
--   Exposedface finrank lt of ssubset
-- statement:
--   Let $P,F,G$ be subsets of $\mathbb R^d$. Assume that $F$ is a nonempty exposed face of $P$ and $F\subsetneq G\subseteq P$. Then
--
--   $$\dim\operatorname{aff}(F)<\dim\operatorname{aff}(G).$$
--
--   Neither compactness nor convexity of $P$ or $G$ is required. The result supplies strict rank growth for chains in exposed-face posets, as needed when recovering face dimensions from the inclusion order.
-- source:
--   Elementary consequence of the exposed-face definition in Mathlib/Analysis/Convex/Exposed.lean, IsExposed; supporting Grünbaum (2003), §2.4 and §12.3, Theorem 12.3.1. https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/Convex/Exposed.lean

import Mathlib.Analysis.Convex.Exposed
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

set_option autoImplicit false

namespace Grunbaum2003

theorem exposedFace_finrank_lt_of_ssubset {d : ℕ}
    {P F G : Set (Fin d → ℝ)} (hF : IsExposed ℝ P F)
    (hFne : F.Nonempty) (hFG : F ⊂ G) (hGP : G ⊆ P) :
    Module.finrank ℝ (affineSpan ℝ F).direction <
      Module.finrank ℝ (affineSpan ℝ G).direction := by sorry

end Grunbaum2003
