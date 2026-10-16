-- Prove2me | Theorems.Thm_OAI_ComplexCancellation_BezoutFrame_exists_frame
-- name    : OAI.ComplexCancellation.BezoutFrame.exists_frame
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T19:59:48.406043+00:00
-- url     : https://prove2.me/theorems/010ab574-8169-4912-a649-98c2f9ef2961
-- title:
--   Points of the quadric $xy=z(z+1)$ over a Euclidean domain lift to $\mathrm{SL}_2$
-- statement:
--   Let $R$ be a Euclidean domain and let $x,y,z\in R$ satisfy $xy=z(z+1)$. Then there exist $a,b,c,d\in R$ with
--
--   $$
--   ab=x,\qquad dc=y,\qquad db=z,\qquad ac-db=1 .
--   $$
--
--   In other words, the matrix $\begin{pmatrix}a&b\\ d&c\end{pmatrix}$ lies in $\mathrm{SL}_2(R)$ and is mapped to $(x,y,z)$ by $\begin{pmatrix}a&b\\ d&c\end{pmatrix}\mapsto(ab,dc,db)$. This map is invariant under right multiplication by the diagonal torus and takes values in the quadric $xy=z(z+1)$, since $z+1=ac$; the theorem says that over a Euclidean domain it is surjective on points.
--
--   In the cancellation argument the theorem is applied over a polynomial ring in one variable over a field (the field of constants of a derivation), which is a Euclidean domain, to produce an explicit $\mathrm{SL}_2$-frame for a point of the quadric $xy=z(z+1)$.
--
--   **Formalization Note** The existential is ordered as `∃ a d b c : R`, and the four conclusions are `a*b = x`, `d*c = y`, `d*b = z` and `a*c - d*b = 1`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Algebra/AffineCancellation/BezoutFrame.lean#L9-L44

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

open OAI OAI.ComplexCancellation

theorem OAI.ComplexCancellation.BezoutFrame.exists_frame {R : Type*} [EuclideanDomain R] (x y z : R)
    (h : x*y = z*(z+1)) :
    ∃ a d b c : R, a*b = x ∧ d*c = y ∧ d*b = z ∧ a*c-d*b = 1 := by sorry
