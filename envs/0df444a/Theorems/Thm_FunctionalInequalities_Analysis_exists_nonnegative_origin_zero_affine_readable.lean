-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_exists_nonnegative_origin_zero_affine_readable
-- name    : FunctionalInequalities.Analysis.exists_nonnegative_origin_zero_affine_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:04:21.379606+00:00
-- url     : https://prove2.me/theorems/23dc8e13-df9f-4967-b282-729c3b46dcf2
-- title:
--   Nonnegative Affine Normalization of a Convex Potential
-- statement:
--   This is a pointwise affine-normalization lemma supporting Proposition 12 of Cordero–Erausquin–Klartag (CorderoKlartag2015).
--
--   Let $E$ be finite-dimensional, let $f:E\to\overline{\mathbb R}$ be a `ConvexPotential`, and assume $0$ lies in the interior of its finite effective domain. Then there exists $a\in E$ such that, for $g=\operatorname{affineSubtract}(f,a,(f(0))_{\mathrm{toReal}})$, $g$ is a `ConvexPotential` and
--
--   $$0\le g(x)\quad\text{for every }x\in E,\qquad g(0)=0.$$
--
--   The conclusion concerns only pointwise normalization and does not involve measures or integrals.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem exists_nonnegative_origin_zero_affine [FiniteDimensional ℝ E]
--       (f : E → EReal) (hf : ConvexPotential f)
--       (h0 : (0 : E) ∈ interior {x | f x ≠ ⊤}) :
--       ∃ a : E, let g := affineSubtract f a (f 0).toReal
--         ConvexPotential g ∧ (∀ x, 0 ≤ g x) ∧ g 0 = 0
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/Convex/Affine`](https://prove2.me/theorems/ba0d4420-d959-4afc-bf5b-05caa7b55a1c).
--
--   Definition modules: [`Analysis/Convex/Legendre`](https://prove2.me/theorems/ccf34d51-1332-4642-a3a3-dacdd0cbab81).
--
--   Supporting theorems: [`convex_epigraph_affineSubtract`](https://prove2.me/theorems/ddb03546-bc6f-456e-b9a9-168872a634c9), [`exists_supporting_affine_at_zero`](https://prove2.me/theorems/97b64fff-d78e-4e36-95a6-0b28ffa54f3d).
--
--   Previous: [`convex_epigraph_affineSubtract`](https://prove2.me/theorems/ddb03546-bc6f-456e-b9a9-168872a634c9).
--
--   [Source excerpt, lines 124–128](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Convex/Affine.lean#L124-L128) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Convex/Affine.lean#L122-L140 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Convex.Affine`, declaration `FunctionalInequalities.Analysis.exists_nonnegative_origin_zero_affine`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Convex_Affine

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem FunctionalInequalities.Analysis.exists_nonnegative_origin_zero_affine_readable [FiniteDimensional ℝ E]
    (f : E → EReal) (hf : ConvexPotential f)
    (h0 : (0 : E) ∈ interior {x | f x ≠ ⊤}) :
    ∃ a : E, let g := affineSubtract f a (f 0).toReal
      ConvexPotential g ∧ (∀ x, 0 ≤ g x) ∧ g 0 = 0 := by sorry
