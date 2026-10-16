-- Prove2me | Theorems.Thm_OAI_ComplexCancellation_Bundle_pullback_graded
-- name    : OAI.ComplexCancellation.Bundle.pullback_graded
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T20:21:01.066293+00:00
-- url     : https://prove2.me/theorems/d9ce3b36-caf6-4820-8388-5b7b36d671b2
-- title:
--   The pullback $\psi$ from the degenerate hypersurface $G$ to the bundle ring is graded
-- statement:
--   Let $G = \mathbb{C}[p,s,u,F,J]/(H_0)$, where $x = s^2 + u^3 + p^2F$ and $H_0 = x^2F - (1 + 2sx)J - p^2J^2$; thus $G$ is obtained from the hypersurface ring $A = \mathbb{C}[p,s,u,F,J]/\big(x^2F - (1+2sx)J - p^2J^2 - pu\big)$ with $x = s^2 + u^3 + p^2F$ by dropping the term $-pu$ from the defining equation. Give the variables the weights $\mathrm{wt}(p) = -1$, $\mathrm{wt}(s) = \mathrm{wt}(u) = 0$ and $\mathrm{wt}(F) = \mathrm{wt}(J) = 2$. Then $x$ is weighted homogeneous of weight $0$ and $H_0$ of weight $2$, so $G$ inherits a $\mathbb{Z}$-grading whose piece $G_i$ is the image of the weighted homogeneous polynomials of weight $i$.
--
--   Let $S = \mathbb{C}[a,b,c,d,u]/(ac - bd - 1)$, let $v = a^3b - a^2u^3 - d^2 \in S$, and let $B = S[\tau,V]/(\tau^2V - v)$ (the bundle ring), with $S$ identified with its image in $B$. Grade $B$ with $S$ in degree $0$, $\deg\tau = -1$ and $\deg V = 2$, so that $B_i$ is the $S$-span of the monomials $\tau^mV^n$ with $2n - m = i$. Let $\psi : G \to B$ be the $\mathbb{C}$-algebra homomorphism (the pullback) determined by $\psi(p) = \tau$, $\psi(s) = dc - ab(ab - u^3)$, $\psi(u) = u$, $\psi(F) = C_1V$ and $\psi(J) = b^2V$, where $C_1 = c^2 - b^2(ab - u^3)$.
--
--   Then $\psi$ is a homomorphism of graded algebras: for every $i \in \mathbb{Z}$ and every $r \in G$,
--
--   $$
--   r \in G_i \ \Longrightarrow\ \psi(r) \in B_i .
--   $$
--
--   In the proof that $A$ is not a polynomial ring in four variables, a nonzero homogeneous element of positive degree in the kernel of a locally nilpotent derivation of $G$ is transported by the injective map $\psi$ to a nonzero homogeneous element of the same positive degree in $B$, where a positive-degree obstruction applies.
--
--   **Formalization Note** $G_i$ is `Degeneration.pieces i` (weights `Degeneration.weight`), $B_i$ is `Bundle.valuationPieces i`, and $\psi$ is `Bundle.pullback`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Algebra/AffineCancellation/BundleGrading.lean#L33-L52

import Mathlib
import Definitions.Def_ComplexCancellation
import Definitions.Def_OAI_Algebra_AffineCancellation_CylinderShift
import Definitions.Def_OAI_Algebra_AffineCancellation_CylinderMaps
import Definitions.Def_OAI_Algebra_AffineCancellation_Cylinder
import Definitions.Def_OAI_Algebra_AffineCancellation_Dimension
import Definitions.Def_OAI_Algebra_AffineCancellation_FactorDerivation
import Definitions.Def_OAI_Algebra_AffineCancellation_Orbit
import Definitions.Def_OAI_Algebra_AffineCancellation_Order
import Definitions.Def_OAI_Algebra_AffineCancellation_LaurentDerivation
import Definitions.Def_OAI_Algebra_AffineCancellation_Clearing
import Definitions.Def_OAI_Algebra_AffineCancellation_GradedLND
import Definitions.Def_OAI_Algebra_AffineCancellation_QuotientGrading
import Definitions.Def_OAI_Algebra_AffineCancellation_QuotientDerivation
import Definitions.Def_OAI_Algebra_AffineCancellation_Determinant
import Definitions.Def_OAI_Algebra_AffineCancellation_DeterminantRigidity
import Definitions.Def_OAI_Algebra_AffineCancellation_Quadric
import Definitions.Def_OAI_Algebra_AffineCancellation_Degeneration
import Definitions.Def_OAI_Algebra_AffineCancellation_Rees
import Definitions.Def_OAI_Algebra_AffineCancellation_ReesReduction
import Definitions.Def_OAI_Algebra_AffineCancellation_ReesDerivation
import Definitions.Def_OAI_Algebra_AffineCancellation_DegenerationGrading
import Definitions.Def_OAI_Algebra_AffineCancellation_ReesGrading
import Definitions.Def_OAI_Algebra_AffineCancellation_PositiveInvariant
import Definitions.Def_OAI_Algebra_AffineCancellation_RelativeClearing
import Definitions.Def_OAI_Algebra_AffineCancellation_FractionDerivation
import Definitions.Def_OAI_Algebra_AffineCancellation_DifferentialSlice
import Definitions.Def_OAI_Algebra_AffineCancellation_RationalSlice
import Definitions.Def_OAI_Algebra_AffineCancellation_PolynomialSlice
import Definitions.Def_OAI_Algebra_AffineCancellation_Modification
import Definitions.Def_OAI_Algebra_AffineCancellation_Bundle
import Definitions.Def_OAI_Algebra_AffineCancellation_ModificationGrading
import Definitions.Def_OAI_Algebra_AffineCancellation_PolynomialDerivation
import Definitions.Def_OAI_Algebra_AffineCancellation_Extraction
import Definitions.Def_OAI_Algebra_AffineCancellation_PositiveObstruction
import Definitions.Def_OAI_Algebra_AffineCancellation_TorsorFrame
import Definitions.Def_OAI_Algebra_AffineCancellation_TorsorInverse
import Definitions.Def_OAI_Algebra_AffineCancellation_ReplicaLift
import Definitions.Def_OAI_Algebra_AffineCancellation_LaurentEuler
import Definitions.Def_OAI_Algebra_AffineCancellation_Intertwining

open OAI OAI.ComplexCancellation OAI.ComplexCancellation.Bundle
open Determinant

theorem OAI.ComplexCancellation.Bundle.pullback_graded (i : ℤ) (r : Degeneration.G) (hr : r ∈ Degeneration.pieces i) :
    pullback r ∈ valuationPieces i := by sorry
