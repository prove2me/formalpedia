-- Prove2me | Theorems.Thm_OAI_ComplexCancellation_Bundle_fiberEuler_homogeneous
-- name    : OAI.ComplexCancellation.Bundle.fiberEuler_homogeneous
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T20:16:52.962465+00:00
-- url     : https://prove2.me/theorems/ead5e9fc-27d1-4fc6-b24d-8f72969c6c7b
-- title:
--   The fiber Euler derivation of the bundle ring preserves the $\mathbb{Z}$-grading
-- statement:
--   Let $S = \mathbb{C}[a,b,c,d,u]/(ac - bd - 1)$, let $v = a^3b - a^2u^3 - d^2 \in S$, and let $B = S[\tau,V]/(\tau^2V - v)$ (the bundle ring), with $S$ identified with its image in $B$. Grade $B$ by $\mathbb{Z}$ with $S$ in degree $0$, $\deg\tau = -1$ and $\deg V = 2$: the piece $B_i$ is the $S$-span of the monomials $\tau^mV^n$ with $2n - m = i$ (the image of the weighted homogeneous polynomials of weight $i$).
--
--   Let $\varepsilon$ be the Euler derivation of $S$, i.e. the $\mathbb{C}$-derivation with $\varepsilon(a) = a$, $\varepsilon(d) = d$, $\varepsilon(b) = -b$, $\varepsilon(c) = -c$ and $\varepsilon(u) = 0$; it satisfies $\varepsilon(v) = 2v$. The fiber Euler derivation $\hat\varepsilon$ of $B$ is the $\mathbb{C}$-derivation that agrees with $\varepsilon$ on $S$ and satisfies $\hat\varepsilon(\tau) = 0$ and $\hat\varepsilon(V) = 2V$ (it is well defined because it sends $\tau^2V - v$ to $2(\tau^2V - v)$).
--
--   Then $\hat\varepsilon$ preserves the grading: for every $i \in \mathbb{Z}$ and every $r \in B$,
--
--   $$
--   r \in B_i \ \Longrightarrow\ \hat\varepsilon(r) \in B_i .
--   $$
--
--   So $\hat\varepsilon$ is a homogeneous derivation of degree $0$. This makes the grading compatible with equivariance: if a derivation of $B$ commutes with $\hat\varepsilon$, then so does each of its homogeneous components. In the proof that the hypersurface ring $A = \mathbb{C}[p,s,u,F,J]/\big(x^2F - (1+2sx)J - p^2J^2 - pu\big)$ with $x = s^2 + u^3 + p^2F$ is not a polynomial ring in four variables, this is applied to the top homogeneous component of a lifted locally nilpotent derivation of $B$.
--
--   **Formalization Note** $B$ is `Bundle.B`, $B_i$ is `valuationPieces i` (the pieces `AffineModification.pieces` of the modification, viewed as $\mathbb{C}$-submodules), and $\hat\varepsilon$ is `fiberEuler`, i.e. `AffineModification.euler v Euler Euler_v`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Algebra/AffineCancellation/BundleGrading.lean#L16-L32

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

theorem OAI.ComplexCancellation.Bundle.fiberEuler_homogeneous (i : ℤ) (r : B) (hr : r ∈ valuationPieces i) :
    fiberEuler r ∈ valuationPieces i := by sorry
