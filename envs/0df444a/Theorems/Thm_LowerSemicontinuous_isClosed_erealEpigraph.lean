-- Prove2me | Theorems.Thm_LowerSemicontinuous_isClosed_erealEpigraph
-- name    : LowerSemicontinuous.isClosed_erealEpigraph
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-27T00:30:37.388732+00:00
-- url     : https://prove2.me/theorems/5be6b59a-aa8e-4b9e-b962-fb17a48f3e9e
-- title:
--   The epigraph of a lower semicontinuous `EReal`-valued function is closed
-- statement:
--   Let $E$ be a real normed space and let $f : E \to \overline{\mathbb{R}}$ be an extended-
--   real-valued function on it. If $f$ is lower semicontinuous, then its epigraph, taken with a
--   *real* second coordinate,
--
--   $$
--   \operatorname{epi} f \;=\; \bigl\{ (x, r) \in E \times \mathbb{R} \;:\; f(x) \le r \bigr\},
--   $$
--
--   is a closed subset of $E \times \mathbb{R}$.
--
--   Lower semicontinuity of a function and closedness of its epigraph are two faces of the same
--   condition, and this is the direction one needs in practice: separation theorems, the existence
--   of affine minorants and the construction of conjugate functions are all applied to the epigraph
--   as a closed convex set. Stating it with a real second coordinate, rather than an extended-real
--   one, is what makes it usable together with the Hahn–Banach theorem in $E \times
--   \mathbb{R}$.
--
--   **Formalization Note** $f$ has type `E → EReal` and the comparison `f p.1 ≤ (p.2 :
--   EReal)` coerces the real second coordinate; no convexity or properness is assumed.
-- source:
--   R. T. Rockafellar, Convex Analysis, Princeton 1970, Theorem 7.1; carved from the accepted proof of RockafellarMaxMono.Cyclic.maximal_cyclically_monotone_iff_subdiff, https://prove2.me/submissions/23d86335-ed0d-406b-b7dd-748579bde0b9

import Mathlib

set_option autoImplicit false

theorem LowerSemicontinuous.isClosed_erealEpigraph {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : E → EReal)
    (hlsc : LowerSemicontinuous f) :
    IsClosed {p : E × ℝ | f p.1 ≤ (p.2 : EReal)} := by sorry
