-- Prove2me | Theorems.Thm_OAI_CanonicalFace198_image_minFace
-- name    : OAI.CanonicalFace198.image_minFace
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T15:45:44.396485+00:00
-- url     : https://prove2.me/theorems/3a9c0a29-90f9-4d3d-989b-b8c8ae0b4133
-- title:
--   Injective affine maps onto a face carry minimal faces to minimal faces
-- statement:
--   Let $A$ and $B$ be real vector spaces. For sets $F\subseteq P\subseteq A$, the set $F$ is an *extreme subset* of $P$ if whenever a point of $F$ lies in the open segment $\{\lambda p_1+(1-\lambda)p_2:\ 0<\lambda<1\}$ between two points $p_1,p_2\in P$, both $p_1$ and $p_2$ belong to $F$. For a set $P\subseteq A$ and a point $x\in A$, the *minimal face* of $P$ at $x$ is the intersection of all convex extreme subsets of $P$ that contain $x$:
--   $$
--   \operatorname{mf}_P(x)=\bigcap\big\{F\subseteq A:\ F\text{ is convex},\ F\text{ is an extreme subset of }P,\ x\in F\big\}.
--   $$
--
--   **Theorem.** Let $f:A\to B$ be an injective affine map, let $P\subseteq A$ and $K\subseteq B$ be convex sets such that $f(P)$ is an extreme subset of $K$, and let $x\in P$. Then
--   $$
--   f\big(\operatorname{mf}_P(x)\big)=\operatorname{mf}_K\big(f(x)\big).
--   $$
--
--   In words: if a convex set $P$ is embedded affinely and injectively onto a face of a convex set $K$, then the smallest face of $K$ through $f(x)$ is exactly the image of the smallest face of $P$ through $x$. No topology, closedness or finite-dimensionality is required. The result transfers minimal faces between a polytope and a copy of it sitting as a face inside a larger polytope, for instance between the perfect matching polytope of a graph and a face of the perfect matching polytope of an expanded graph.
--
--   **Formalization Note** The map is an affine map `A →ᵃ[ℝ] B` together with a proof of `Function.Injective f`. Extremality is Mathlib's `IsExtreme ℝ K (f '' P)`, which asks for the inclusion and only for the first endpoint of the segment to lie in the subset; this is equivalent to the two-endpoint condition above because open segments are symmetric. The minimal face `minFace P x` is defined as the intersection `⋂₀ facesThrough P x` of the family of convex extreme subsets of $P$ containing $x$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/TriangleFace/Faces.lean#L52-L66

import Mathlib
import Definitions.Def_TriangleFace
import Definitions.Def_OAI_Combinatorics_MatchingEntropy_Model
import Definitions.Def_OAI_Combinatorics_MatchingEntropy_Simplex
import Definitions.Def_OAI_Combinatorics_MatchingEntropy_Coupling
import Definitions.Def_OAI_Combinatorics_MatchingEntropy_Basic
import Definitions.Def_OAI_Combinatorics_MatchingEntropy_OddCuts
import Definitions.Def_OAI_Combinatorics_MatchingEntropy_Contraction
import Definitions.Def_OAI_Combinatorics_MatchingEntropy_Polytope
import Definitions.Def_OAI_Combinatorics_MatchingEntropy_Face
import Definitions.Def_OAI_Combinatorics_MatchingEntropy_Entropy
import Definitions.Def_OAI_Combinatorics_MatchingEntropy_Duality
import Definitions.Def_OAI_Combinatorics_MatchingEntropy_EdgeReduction
import Definitions.Def_OAI_Combinatorics_MatchingEntropy_MinimalFace
import Definitions.Def_OAI_Combinatorics_MatchingEntropy_FractionalReduction
import Definitions.Def_OAI_Combinatorics_MatchingEntropy_Components
import Definitions.Def_OAI_Combinatorics_MatchingEntropy_TriangleExpansion

open OAI OAI.CanonicalFace198
variable {A B : Type*} [AddCommGroup A] [Module ℝ A]
  [AddCommGroup B] [Module ℝ B]

theorem OAI.CanonicalFace198.image_minFace (f : A →ᵃ[ℝ] B) (hf : Function.Injective f)
    {P : Set A} {K : Set B} (hP : Convex ℝ P) (hK : Convex ℝ K)
    (hface : IsExtreme ℝ K (f '' P)) {x : A} (hx : x ∈ P) :
    f '' minFace P x = minFace K (f x) := by sorry
