-- Prove2me | Theorems.Thm_OAI_ComplexCancellation_GradedLND_component_locallyNilpotent
-- name    : OAI.ComplexCancellation.GradedLND.component_locallyNilpotent
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T19:48:16.805982+00:00
-- url     : https://prove2.me/theorems/7277f44e-d406-4649-8cd4-f90b093a1e95
-- title:
--   The degree-$j$ component of a locally nilpotent derivation of shift at most $j$ is locally nilpotent
-- statement:
--   Let $k$ be a commutative ring and let $R$ be a commutative $k$-algebra with a $\mathbb{Z}$-grading $R=\bigoplus_{i\in\mathbb{Z}}R_i$ by $k$-submodules compatible with multiplication ($R_iR_{i'}\subseteq R_{i+i'}$ and $1\in R_0$); negative degrees are allowed. Write $\pi_i:R\to R_i$ for the projection onto the degree-$i$ part and, for $d\in\mathbb{Z}$, let $R_{\le d}=\sum_{i\le d}R_i$ be the associated increasing filtration.
--
--   For a $k$-derivation $D$ of $R$ and an integer $j$, the degree-$j$ component of $D$ is the $k$-derivation $D_j$ of $R$ given on homogeneous elements by $D_j(r)=\pi_{i+j}(D(r))$ for $r\in R_i$ and extended additively. Say that $D$ has shift at most $j$ if $D(R_i)\subseteq R_{\le i+j}$ for every $i\in\mathbb{Z}$.
--
--   **Theorem.** Let $D$ be a $k$-derivation of $R$ and $j\in\mathbb{Z}$. Assume that $D$ has shift at most $j$ and that $D$ is locally nilpotent, i.e. for every $r\in R$ there is $n\in\mathbb{N}$ with $D^n(r)=0$. Then $D_j$ is locally nilpotent:
--
--   $$
--   \forall r\in R\ \ \exists n\in\mathbb{N}:\qquad D_j^{\,n}(r)=0 .
--   $$
--
--   If $R$ is finitely generated and $D\neq0$, there is a largest $j$ with $D_j\neq0$, and $D$ then has shift at most $j$; in that situation $D_j$ is the highest homogeneous component (the leading form) of $D$. The theorem says that this leading form inherits local nilpotence, which is the standard device for replacing an arbitrary locally nilpotent derivation by a homogeneous one when proving rigidity of graded algebras.
--
--   **Formalization Note** The grading is `G : ℤ → Submodule k R` with `[GradedAlgebra G]`, $\pi_i$ is `GradedAlgebra.proj G i`, the filtration is `filtration G d` (a supremum of submodules), the shift condition is `ShiftBound G D j`, and $D_j$ is `component G D j`. Local nilpotence is written out with function iteration, `∀ r, ∃ n, D^[n] r = 0`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Algebra/AffineCancellation/GradedLND.lean#L155-L184

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

open OAI OAI.ComplexCancellation OAI.ComplexCancellation.GradedLND
open DirectSum
variable {k R : Type*} [CommRing k] [CommRing R] [Algebra k R]
variable (G : ℤ → Submodule k R) [GradedAlgebra G]

theorem OAI.ComplexCancellation.GradedLND.component_locallyNilpotent {D : Derivation k R R} {j : ℤ}
    (hD : ShiftBound G D j) (hln : ∀ r : R, ∃ n : ℕ, (D : R → R)^[n] r = 0) :
    ∀ r : R, ∃ n : ℕ, (component G D j : R → R)^[n] r = 0 := by sorry
