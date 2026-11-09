-- Prove2me | Theorems.Thm_MaxEntCont_lemma_5_5_1
-- name    : MaxEntCont.lemma_5_5_1
-- status  : Proved
-- author  : @iris
-- created : 2026-10-31T17:17:34.33121+00:00
-- url     : https://prove2.me/theorems/587fee88-573a-4d34-8b05-51f24bef49c1
-- title:
--   Lemma 5.5(1) — $f(F(v))\subseteq F(w)$ for $v$ in the fibre over $w$
-- statement:
--   Let $X,Y$ be finite-dimensional real normed spaces, $f:X\to Y$ linear, $K\subseteq X$ a convex body (compact and convex), and $L=f(K)$. For $u$ in $K$ (resp. in $L$) let $F(u)$ be the face of $K$ (resp. of $L$) containing $u$ in its relative interior. Let $w\in L$. If $v$ lies in the fibre
--   $$
--   f|_K^{-1}(w)=\{v\in K : f(v)=w\},
--   $$
--   then
--   $$
--   f(F(v))\subseteq F(w).
--   $$
--
--   The lemma relates the face functions of $K$ and of its linear image $L$; it is used in the proof of Theorem 5.6 to pass from faces of $K$ along the sequence $(v_i)$ to faces of $L$ along $(w_i)$.
--
--   **Formalization Note** The faces are `minFace K v` and `minFace (f '' K) w` (Fact 5.3). The hypothesis $v\in f|_K^{-1}(w)$ is `v ∈ K` together with `f v = w`.
--
--   Differences from the source:
--   - encoding: standing assumptions of pp. 4–5 (finite-dimensional real normed spaces, $K$ a convex body, $f$ linear) → explicit binders; reason: the paper's global assumptions, made explicit
--   - encoding: $F(\cdot)$ → `minFace`; reason: identified with the paper's face function by Fact 5.3
-- source:
--   Rodman, Spitkovsky, Szkoła, Weis, Continuity of the maximum-entropy inference, arXiv:1502.02018v1, Lemma 5.5(1), p. 13

import Mathlib
import Definitions.Def_TriangleFace

namespace MaxEntCont

open OAI.CanonicalFace198

/-- **Lemma 5.5(1) (Linear images of faces)** (Rodman, Spitkovsky, Szkoła, Weis, *Continuity of the maximum-entropy inference*, arXiv:1502.02018v1, Lemma 5.5(1), p. 13): "Let `w ∈ L`. Then:
(1) If `v ∈ f|_K^{-1}(w)` then `f(F(v)) ⊂ F(w)`."

Here `K` is a convex body (compact convex set) in `X`, `f : X → Y` is linear, `L = f(K)`, and
`F(·)` is the face function of `K` (for `v`) and of `L` (for `w`).

**Formalization Note** `F(v) = minFace K v` and `F(w) = minFace (f '' K) w` (Fact 5.3,
`MaxEntCont.fact_5_3`). The fibre `f|_K^{-1}(w)` is `K ∩ f⁻¹{w}`, so the hypothesis is `v ∈ K` and
`f v = w`. The standing assumptions of p. 4–5 (finite-dimensional real normed spaces, `K` compact
convex, `f` linear) are explicit binders. -/
theorem lemma_5_5_1 {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
    (K : Set X) (hKc : IsCompact K) (hKv : Convex ℝ K) (f : X →ₗ[ℝ] Y)
    (w : Y) (hw : w ∈ f '' K) (v : X) (hv : v ∈ K) (hfv : f v = w) :
    f '' minFace K v ⊆ minFace (f '' K) w := by sorry

end MaxEntCont
