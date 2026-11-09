-- Prove2me | Theorems.Thm_FourBlockIP_FPT_lemma_4
-- name    : FourBlockIP.FPT.lemma_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:39:56.757219+00:00
-- url     : https://prove2.me/theorems/ed67a578-d9d4-4035-b71c-e2e46a0ee346
-- title:
--   Lemma 4 — IDP dilation iff value-function convex extensibility
-- statement:
--   Let $\mathcal A$ be a class of integer matrices closed under inverting columns, and let $M\ge0$ be an integer. Then
--
--   $$\mathcal A\text{ has IDP after an }M\text{-dilation}\quad\Longleftrightarrow\quad
--    h(z)=\inf\{f(x):Ax=r+Mz,\ x\in\mathbb Z^n\}\text{ is convex extensible on }\mathbb Z^m\cap L$$
--
--   for every $m$-by-$n$ matrix $A\in\mathcal A$, every separable convex $f:\mathbb R^n\to\mathbb R\cup\{+\infty\}$, every integer offset $r$, and every affine line $L\subseteq\mathbb R^m$. The extension in this equivalence may take $-\infty$.
--
--   This links the integer decomposition property to the lattice value functions used in the framework. Both directions and $M=0$ remain in the statement.
--
--   Differences from the source:
--   - reading: Lemma 4 allows negative-infinity value functions while p. 3 defines only positive-infinity-valued extensions → convex-epigraph extensions may take either infinity; reason: R3: the column-sign-closed class of rows [±1,±1] has IDP at M=1 but the finite objective -x1 can give h identically negative infinity
--   - encoding: min with empty and unbounded value conventions explained on p. 6 → EReal infimum over the integer feasible image; reason: empty gives top and unbounded below gives bottom, matching the source value conventions
--   - encoding: Euclidean spaces and integer vectors with one-based coordinates → functions on Fin types with zero-based coordinates; reason: finite reindexing changes no instance
-- source:
--   Martin Koutecký, Alexandra Lassota, Koen Ligthart, 4-Block Integer Programming is in FPT, STOC 2027 submission #392 (October 2026), Lemma 4, p. 6; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/392.pdf

import Mathlib
import Definitions.Def_FourBlockIP_FPT_Polyhedra
import Definitions.Def_FourBlockIP_FPT_ValueFunctions

namespace FourBlockIP.FPT

/-- Lemma 4, p. 6, with the EReal convex-epigraph convention (reading R3).
The offset is arbitrary, the line is affine, and M=0 is retained. -/
theorem lemma_4 (cls : MatrixClass) (M : ℕ) (hcls : ClosedUnderInvertingColumns cls) :
    IDPAfterDilation cls M ↔
      ∀ m n (A : Matrix (Fin m) (Fin n) ℤ), (⟨m,n,A⟩ : SizedMatrix) ∈ cls →
        ∀ (f : SepConvexExt n) (r : Fin m → ℤ)
          (L : AffineSubspace ℝ (Fin m → ℝ)), Module.finrank ℝ L.direction = 1 →
          ConvexExtensibleOnExt (valueFn A f r M) {z | castVec z ∈ L} := by sorry

end FourBlockIP.FPT
