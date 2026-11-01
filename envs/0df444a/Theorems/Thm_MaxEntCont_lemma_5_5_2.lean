-- Prove2me | Theorems.Thm_MaxEntCont_lemma_5_5_2
-- name    : MaxEntCont.lemma_5_5_2
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T17:17:42.158659+00:00
-- url     : https://prove2.me/theorems/02ab7966-4aa9-47e7-b2da-b84568cf142e
-- title:
--   Lemma 5.5(2) — $f(F(v))=F(w)$ for $v$ in the relative interior of the fibre
-- statement:
--   Let $X,Y$ be finite-dimensional real normed spaces, $f:X\to Y$ linear, $K\subseteq X$ a convex body (compact and convex), and $L=f(K)$. For $u$ in $K$ (resp. in $L$) let $F(u)$ be the face of $K$ (resp. of $L$) containing $u$ in its relative interior. Let $w\in L$. If $v$ lies in the relative interior of the fibre $f|_K^{-1}(w)=\{v\in K: f(v)=w\}$, then
--   $$
--   f(F(v))=F(w).
--   $$
--
--   Together with Lemma 5.5(1) this says that the face of $L$ through $w$ is the image of the face of $K$ through any relative interior point of the fibre over $w$; Theorem 5.6 uses it at the limit point $v$.
--
--   **Formalization Note** The faces are `minFace K v` and `minFace (f '' K) w` (Fact 5.3); the relative interior is Mathlib's `intrinsicInterior ℝ`, applied to the fibre `K ∩ f ⁻¹' {w}`.
--
--   Differences from the source:
--   - encoding: standing assumptions of pp. 4–5 (finite-dimensional real normed spaces, $K$ a convex body, $f$ linear) → explicit binders; reason: the paper's global assumptions, made explicit
--   - encoding: $F(\cdot)$ → `minFace`; reason: identified with the paper's face function by Fact 5.3
-- source:
--   Rodman, Spitkovsky, Szkoła, Weis, Continuity of the maximum-entropy inference, arXiv:1502.02018v1, Lemma 5.5(2), p. 13

import Mathlib
import Definitions.Def_TriangleFace

namespace MaxEntCont

open OAI.CanonicalFace198

/-- **Lemma 5.5(2) (Linear images of faces)** (Rodman, Spitkovsky, Szkoła, Weis, *Continuity of the maximum-entropy inference*, arXiv:1502.02018v1, Lemma 5.5(2), p. 13): "Let `w ∈ L`. Then: …
(2) If `v ∈ ri(f|_K^{-1}(w))` then `f(F(v)) = F(w)`."

Here `K` is a convex body (compact convex set) in `X`, `f : X → Y` is linear, `L = f(K)`, and
`F(·)` is the face function of `K` (for `v`) and of `L` (for `w`).

**Formalization Note** `F(v) = minFace K v` and `F(w) = minFace (f '' K) w` (Fact 5.3,
`MaxEntCont.fact_5_3`); `ri` is Mathlib's `intrinsicInterior ℝ`, applied to the fibre
`f|_K^{-1}(w) = K ∩ f⁻¹{w}`. The standing assumptions of p. 4–5 (finite-dimensional real normed
spaces, `K` compact convex, `f` linear) are explicit binders. -/
theorem lemma_5_5_2 {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
    (K : Set X) (hKc : IsCompact K) (hKv : Convex ℝ K) (f : X →ₗ[ℝ] Y)
    (w : Y) (hw : w ∈ f '' K) (v : X) (hv : v ∈ intrinsicInterior ℝ (K ∩ f ⁻¹' {w})) :
    f '' minFace K v = minFace (f '' K) w := by sorry

end MaxEntCont
