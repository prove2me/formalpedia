-- Prove2me | Theorems.Thm_K24_Global_coverHolderToBundleContinuity
-- name    : K24.Global.coverHolderToBundleContinuity
-- status  : Proved
-- author  : @xwh
-- created : 2026-10-23T19:20:14.016286+00:00
-- url     : https://prove2.me/theorems/17b315b9-3732-4337-b974-3cfddc181c2f
-- title:
--   K24: bounded-cover Hölder regularity gives native and bundle continuity
-- statement:
--   For every smooth four-manifold, canonical bounded local cover `C`, natural
--   order `k`, and nonnegative exponent `α`, it proves all three implications:
--
--   - `C.Cov2Holder k α U` implies `Cov2ContDiff 0 U` and continuity of the actual
--     function `(p,v,w) ↦ U p v w` on the fiber product of two tangent bundles.
--   - `C.CovectorHolder k α eta` implies `CovectorContDiff 0 eta` and continuity of
--     the actual function `(p,v) ↦ eta p v` on the tangent bundle.
--   - `C.VectorHolder k α Y` implies `VectorContDiff 0 Y` and continuity of the
--     actual tangent-bundle section `p ↦ (p,Y p)`.
--
--   The canonical Hölder predicates are used unchanged. They provide regularity
--   of the literal lifted coefficients on inner cover-chart domains, rather than
--   native chart regularity as an extra field. No native regularity or desired
--   continuity is added as a hypothesis. The proof uses only the continuous part
--   of that coefficient regularity, so the finite norm and positivity of the
--   exponent are unnecessary for this implication. The statement includes order
--   zero and imposes no compactness of the base manifold or new cover-degree bound.
--
--   This closes the previously explicit gap between the original bounded-cover
--   Hölder assumptions and the continuity inputs of the frozen Haar projection
--   result at `7050423f55f4b9f25d4c845a1e6edd9d2f3be67c`. That Haar theorem can now be
--   applied to the original Hölder section hypotheses to derive genuine pointwise
--   Haar integrability and its invariant, idempotent, and zero-average-complement
--   identities for tensors, covectors, and vectors.
--
--   This theorem does not prove higher native differentiability, Hölder regularity
--   of the averages, boundedness in the Hölder norms, Sobolev conclusions, inverse
--   estimates, or flat-torus sharpness. The original K24 root
--   `aac3db7a-b1fb-4137-ab8b-8f9efc4d3b22` and its `FullK24Statement` remain open.
--
--   Supporting original full target https://prove2.me/theorems/aac3db7a-b1fb-4137-ab8b-8f9efc4d3b22 .
-- source:
--   https://github.com/liushuijixiang/siwei-einstein/blob/8c02be189f097080feca952347c9104bfb986242/四维Einstein/75_BRANCH_K_killing_spectrum/K24_FIXED_REFERENCE_CHANGE_OF_SLICE_GATE.md — §1 common pointwise Haar projections; bounded local cover and Hölder coefficient definitions in canonical definition 738f77a5-d72a-4017-95ce-870ad72cb8a2.

import Definitions.Def_K24GlobalAnalysis

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open K24.Global
open scoped Manifold ContDiff NNReal
universe u

theorem K24.Global.coverHolderToBundleContinuity {M : Type u} [TopologicalSpace M] [ChartedSpace FourSpace M]
    [IsManifold I4 ∞ M] (C : BoundedLocalCover M) (k : ℕ) (α : ℝ≥0) :
    (∀ U : RawCov2 M, C.Cov2Holder k α U →
      Cov2ContDiff 0 U ∧
      Continuous (fun q : {q : TangentBundle I4 M × TangentBundle I4 M //
        q.1.proj = q.2.proj} => U q.val.1.proj q.val.1.2 q.val.2.2)) ∧
    (∀ eta : RawCovector M, C.CovectorHolder k α eta →
      CovectorContDiff 0 eta ∧
      Continuous (fun q : TangentBundle I4 M => eta q.proj q.2)) ∧
    (∀ Y : RawVector M, C.VectorHolder k α Y →
      VectorContDiff 0 Y ∧
      Continuous (fun p : M => (⟨p, Y p⟩ : TangentBundle I4 M))) := by sorry
