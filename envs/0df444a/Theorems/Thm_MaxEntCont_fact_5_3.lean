-- Prove2me | Theorems.Thm_MaxEntCont_fact_5_3
-- name    : MaxEntCont.fact_5_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T17:18:04.023695+00:00
-- url     : https://prove2.me/theorems/048269ed-b706-4114-8e53-185d6a93453c
-- title:
--   Fact 5.3 — every point of a convex set lies in the relative interior of a unique face
-- statement:
--   Let $C$ be a convex subset of a finite-dimensional real normed space and let $x\in C$. Then there is a unique face of $C$ that contains $x$ in its relative interior. More precisely, the smallest face $F(x)$ of $C$ containing $x$ (the intersection of all faces of $C$ containing $x$) satisfies:
--
--   1. $F(x)$ is a face of $C$;
--   2. $x\in\operatorname{ri}F(x)$;
--   3. every face $G$ of $C$ with $x\in\operatorname{ri}G$ equals $F(x)$.
--
--   This is what makes the face function $x\mapsto F(x)$ of $C$ well defined, and it identifies the face function with the smallest face through $x$, which is how the face function is represented throughout the mission.
--
--   **Formalization Note** $\operatorname{ri}$ is Mathlib's `intrinsicInterior ℝ`, the interior relative to the affine hull. The smallest face is the platform definition `OAI.CanonicalFace198.minFace C x`.
--
--   Differences from the source:
--   - generalization: there exists a unique face of $C$ containing $x$ in its relative interior → the unique face is named as the smallest face `minFace C x` through $x$; reason: naming the witness implies the existence and uniqueness of the source and fixes the representation of $F(x)$ used by the other items
--   - encoding: all sets lie in a finite-dimensional real normed space (standing assumption, p. 4) → explicit `[FiniteDimensional ℝ X]` binder; reason: the paper's tacit assumption, made explicit
-- source:
--   Rodman, Spitkovsky, Szkoła, Weis, Continuity of the maximum-entropy inference, arXiv:1502.02018v1, Fact 5.3, p. 13 (proved in Rockafellar, Convex Analysis, Thm 18.2)

import Mathlib
import Definitions.Def_TriangleFace
import Definitions.Def_MaxEntCont_IsFace

namespace MaxEntCont

open OAI.CanonicalFace198

/-- **Fact 5.3 (Face function)** (Rodman, Spitkovsky, Szkoła, Weis, *Continuity of the maximum-entropy inference*, arXiv:1502.02018v1, Fact 5.3, p. 13): "For each point `x` in a convex set `C`
there exists a unique face of `C` which contains `x` in the relative interior." (Proved in
Rockafellar, *Convex Analysis*, Thm. 18.2.)

For `x ∈ C`, the smallest face `minFace C x` through `x` is a face of `C`, `x` lies in its relative
interior, and every face `G` of `C` with `x` in its relative interior equals `minFace C x`.

**Formalization Note** The relative interior is Mathlib's `intrinsicInterior ℝ`. The statement
names the unique face as the platform definition `OAI.CanonicalFace198.minFace C x`, which is what
makes `minFace` the paper's face function `F(x)` throughout the mission; existence and uniqueness
are the first two and the third conjunct. The paper's standing assumption (p. 4) that all sets lie in a
finite-dimensional real normed space is explicit. -/
theorem fact_5_3 {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
    (C : Set X) (hC : Convex ℝ C) (x : X) (hx : x ∈ C) :
    IsFace C (minFace C x) ∧ x ∈ intrinsicInterior ℝ (minFace C x) ∧
      ∀ G : Set X, IsFace C G → x ∈ intrinsicInterior ℝ G → G = minFace C x := by sorry

end MaxEntCont
