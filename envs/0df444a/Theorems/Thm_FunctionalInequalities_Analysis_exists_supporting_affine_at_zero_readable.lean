-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_exists_supporting_affine_at_zero_readable
-- name    : FunctionalInequalities.Analysis.exists_supporting_affine_at_zero_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:04:18.577262+00:00
-- url     : https://prove2.me/theorems/97b64fff-d78e-4e36-95a6-0b28ffa54f3d
-- title:
--   Supporting Affine Minorant at the Origin
-- statement:
--   This formalizes a stronger pointwise supporting-plane statement related to Proposition 12 of Cordero–Erausquin–Klartag (CorderoKlartag2015).
--
--   Let $E$ be finite-dimensional, let $f:E\to\overline{\mathbb R}$ be a `ConvexPotential`, and assume $0$ lies in the interior of $\{x:f(x)\ne+\infty\}$. Then there exists $a\in E$ such that, for every $x\in E$,
--
--   $$\langle a,x\rangle+(f(0))_{\mathrm{toReal}}\le f(x),$$
--
--   where the affine expression is embedded into the extended reals. This is a pointwise supporting affine minorant and is not the variational maximizer assertion of the cited proposition.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem exists_supporting_affine_at_zero [FiniteDimensional ℝ E]
--       (f : E → EReal) (hf : ConvexPotential f)
--       (h0 : (0 : E) ∈ interior {x | f x ≠ ⊤}) :
--       ∃ a : E, ∀ x, ((inner ℝ a x + (f 0).toReal : ℝ) : EReal) ≤ f x
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/Convex/SupportingPlane`](https://prove2.me/theorems/49dea8f8-70b2-49f6-b236-fded64ed171f).
--
--   Definition modules: [`Analysis/Convex/Legendre`](https://prove2.me/theorems/ccf34d51-1332-4642-a3a3-dacdd0cbab81).
--
--   [Source excerpt, lines 76–79](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Convex/SupportingPlane.lean#L76-L79) · Frozen source `408915f`.
-- source:
--   Source: Cordero-Erausquin–Klartag, Moment measures (arXiv:1304.0630v1), Proposition 12. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Convex/SupportingPlane.lean#L74-L183 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Convex.SupportingPlane`, declaration `FunctionalInequalities.Analysis.exists_supporting_affine_at_zero`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Convex_SupportingPlane

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem FunctionalInequalities.Analysis.exists_supporting_affine_at_zero_readable [FiniteDimensional ℝ E]
    (f : E → EReal) (hf : ConvexPotential f)
    (h0 : (0 : E) ∈ interior {x | f x ≠ ⊤}) :
    ∃ a : E, ∀ x, ((inner ℝ a x + (f 0).toReal : ℝ) : EReal) ≤ f x := by sorry
