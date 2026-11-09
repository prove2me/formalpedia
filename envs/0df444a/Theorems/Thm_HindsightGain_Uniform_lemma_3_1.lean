-- Prove2me | Theorems.Thm_HindsightGain_Uniform_lemma_3_1
-- name    : HindsightGain.Uniform.lemma_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:53:00.529559+00:00
-- url     : https://prove2.me/theorems/2869e969-a2dd-4feb-b078-7f586f129aa0
-- title:
--   Lemma 3.1 — Comparison principle
-- statement:
--   Let $r\ge2$, let $E$ be a finite-dimensional real Euclidean space and $T$ a symmetric $r$-linear form. Put $f_T(x)=T(x,\ldots,x)$ and let $L$ be its coefficient matrix with its first coordinate as row. Let $Z$ be nonempty and compact, and $Z'$ nonempty, compact and convex. If $y\in Z$ maximizes $f_T$ on $Z$, then there exists $z\in Z'$ such that, for $W(y,z)=\sum_{k=0}^{r-1}y^{\otimes k}\otimes z^{\otimes(r-1-k)}$,
--   $$\max_Z f_T-\max_{Z'}f_T\le h_Z(LW(y,z))-h_{Z'}(LW(y,z)).$$
--   Here $h_B(v)=\max_{u\in B}\langle u,v\rangle$ and the zeroth tensor power is $1$. Only the reference set $Z'$ is convex. This compares optimal values through a support direction for an arbitrary symmetric form.
--
--   Differences from the source:
--   - encoding: a symmetric r-linear form on a Euclidean space E → a permutation-invariant coefficient array over an arbitrary finite coordinate type with Euclidean array norm; reason: every finite-dimensional real Euclidean space has an orthonormal coordinate representation, including dimension zero
--   - encoding: L and W defined by (14) and (17), and compact-set maxima → explicit coefficient reshaping and tensor coordinate products, with real sSup for maxima and supports; reason: these constructions are the source objects, and all extrema have nonempty compact domains
-- source:
--   Xiaohui Bei, Wenhao Wu, The Optimizer's Windfall: Bounding Hindsight Gain under Random Restrictions, STOC 2027 submission #464 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/464.pdf, Lemma 3.1, (17)–(18), p.15

import Mathlib
import Definitions.Def_HindsightGain_Uniform_tensors

set_option autoImplicit false

namespace HindsightGain.Uniform

/-- Lemma 3.1, (17)-(18), p.15, in arbitrary finite orthonormal coordinates. -/
theorem lemma_3_1 {ι : Type} [Fintype ι] {r : ℕ} (hr : 2 ≤ r)
    (C : Tensor ι r) (hC : symmetric C)
    (Z Z' : Set (EuclideanSpace ℝ ι))
    (hZ : Z.Nonempty) (hZc : IsCompact Z)
    (hZ' : Z'.Nonempty) (hZ'c : IsCompact Z') (hconv : Convex ℝ Z')
    (y : EuclideanSpace ℝ ι) (hy : y ∈ Z)
    (hmax : ∀ x ∈ Z, diagonal C x ≤ diagonal C y) :
    ∃ z ∈ Z', polynomialMax C Z - polynomialMax C Z' ≤
      support Z (tensorL C (comparisonTensor r y z)) -
        support Z' (tensorL C (comparisonTensor r y z)) := by sorry

end HindsightGain.Uniform
