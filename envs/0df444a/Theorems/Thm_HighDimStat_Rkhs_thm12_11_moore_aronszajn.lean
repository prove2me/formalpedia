-- Prove2me | Theorems.Thm_HighDimStat_Rkhs_thm12_11_moore_aronszajn
-- name    : HighDimStat.Rkhs.thm12_11_moore_aronszajn
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-19T23:27:02.002867+00:00
-- url     : https://prove2.me/theorems/d1739662-4990-4d0e-a884-fd50d694d589
-- title:
--   Existence and uniqueness of the RKHS associated with a PSD kernel (Theorem 12.11)
-- statement:
--   **Theorem 12.11 (the Moore-Aronszajn theorem).** The chapter's central existence-and-
--   uniqueness result: every positive semidefinite kernel function determines one Hilbert
--   space of functions, with no further data needed.
--
--   Given any positive semidefinite kernel function $K:X\times X\to\mathbb R$, there is a
--   Hilbert space $H$ of functions on $X$ (embedded via an injective linear map into
--   $X\to\mathbb R$) in which $K$ satisfies the reproducing property (12.3) via a feature map
--   $x\mapsto K(\cdot,x)\in H$ — and this Hilbert space is **unique**: any two Hilbert spaces
--   with the reproducing property for the same $K$ are linearly isometric, via an isometry
--   that intertwines their embeddings into functions on $X$ (so they are, in the sense that
--   matters, literally the same space of functions). It is known as the *reproducing kernel
--   Hilbert space* (RKHS) associated with $K$.
--
--   **Formalization Note** Existence and uniqueness are both formalized, per this chapter's
--   named pitfall that the uniqueness clause is real content. Existence is `∃ H` together with
--   its Hilbert-space instances and the embedding/feature data. Uniqueness is stated as: for
--   any two witnesses $(H_1,\ldots)$ and $(H_2,\ldots)$ of the reproducing property for the
--   same $K$, there is a linear isometric equivalence $e:H_1\simeq_{\ell i} H_2$ with
--   $\mathrm{toFun}_2\circ e = \mathrm{toFun}_1$ — the book's own proof concludes literally
--   $H=G$ (as sets of functions with the same inner product), which this captures as
--   "isometric via an equivalence commuting with the embeddings into functions," the natural
--   formal rendering of literal set equality once $H$ is presented abstractly rather than as
--   a concrete subtype of $X\to\mathbb R$. `X` carries no topology or measure-theoretic
--   structure, matching the chapter's own remark that Theorem 12.11 holds for *any* PSD
--   kernel on *any* set — not conflated with Mercer's theorem's additional compactness and
--   continuity hypotheses.
-- source:
--   Wainwright, High-Dimensional Statistics, CUP 2019, p. 389 (PDF p. 409), Theorem 12.11, Eq. (12.3)

import Mathlib
import Definitions.Def_HighDimStat_Rkhs_Core

namespace HighDimStat.Rkhs

open scoped RealInnerProductSpace

/-- Theorem 12.11 (the Moore-Aronszajn theorem, p. 389): given any positive semidefinite
kernel function `K` on `X`, there is a Hilbert space `H` (embedded into functions on `X` via
`toFun`) in which the kernel satisfies the reproducing property (12.3) via a feature map
`feature`, and this Hilbert space is unique: any two such Hilbert spaces for the same `K` are
linearly isometric via an equivalence that intertwines their embeddings into functions on
`X`. -/
theorem thm12_11_moore_aronszajn {X : Type*} (K : X → X → ℝ) (hK : IsPSDKernel K) :
    (∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℝ H) (_ : CompleteSpace H)
        (toFun : H →ₗ[ℝ] (X → ℝ)) (feature : X → H), IsRKHS K toFun feature) ∧
      (∀ (H₁ : Type) (_ : NormedAddCommGroup H₁) (_ : InnerProductSpace ℝ H₁)
          (_ : CompleteSpace H₁) (toFun₁ : H₁ →ₗ[ℝ] (X → ℝ)) (feature₁ : X → H₁),
          IsRKHS K toFun₁ feature₁ →
        ∀ (H₂ : Type) (_ : NormedAddCommGroup H₂) (_ : InnerProductSpace ℝ H₂)
          (_ : CompleteSpace H₂) (toFun₂ : H₂ →ₗ[ℝ] (X → ℝ)) (feature₂ : X → H₂),
          IsRKHS K toFun₂ feature₂ →
        ∃ e : H₁ ≃ₗᵢ[ℝ] H₂, ∀ f : H₁, toFun₂ (e f) = toFun₁ f) := by sorry

end HighDimStat.Rkhs
