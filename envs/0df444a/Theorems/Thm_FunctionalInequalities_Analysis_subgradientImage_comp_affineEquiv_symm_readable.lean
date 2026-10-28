-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_subgradientImage_comp_affineEquiv_symm_readable
-- name    : FunctionalInequalities.Analysis.subgradientImage_comp_affineEquiv_symm_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:03:45.535634+00:00
-- url     : https://prove2.me/theorems/3ad116ee-9145-4587-a1b0-81a8f51d65df
-- title:
--   Affine Transport of Subgradient Images
-- statement:
--   This establishes the affine transport law for subgradient images.
--
--   Let $E$ be a finite-dimensional real inner-product space, let $u:E\to\mathbb R$, let $e:E\simeq_A E$ be an affine equivalence, and let $G\subseteq E$. If $T=e.linear$ is the linear part of $e$, then
--
--   $$
--   \operatorname{subgradientImage}(u\circ e^{-1},e(G))
--   =
--   \operatorname{adj}(T^{-1})\big(\operatorname{subgradientImage}(u,G)\big).
--   $$
--
--   The image on the right is the set image under the adjoint of the inverse linear part. The declaration is `subgradientImage_comp_affineEquiv_symm_readable`; it is an exact set equality and does not involve volume or determinant factors.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem subgradientImage_comp_affineEquiv_symm (u : E → ℝ) (e : E ≃ᵃ[ℝ] E) (G : Set E) :
--       subgradientImage (u ∘ e.symm) (e '' G) =
--         (LinearMap.adjoint (e.linear.symm : E →ₗ[ℝ] E)) '' subgradientImage u G
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/Convex/Alexandrov`](https://prove2.me/theorems/3d12d62d-28ee-413a-8964-1771fdfa5905).
--
--   Definition modules: [`Analysis/Convex/Subgradient`](https://prove2.me/theorems/67a77afb-a546-4173-875a-237133f9cad7).
--
--   Previous: [`infDist_frontier_le_of_forall_inner_le`](https://prove2.me/theorems/bd9c0578-bb14-4e91-95ff-70001c4a6fce) · Next: [`volume_subgradientImage_comp_affineEquiv_symm`](https://prove2.me/theorems/17cd1bb9-8c78-49af-a2a8-52c8ebcc13dc).
--
--   [Source excerpt, lines 1774–1776](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Convex/Alexandrov.lean#L1774-L1776) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Convex/Alexandrov.lean#L1771-L1856 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Convex.Alexandrov`, declaration `FunctionalInequalities.Analysis.subgradientImage_comp_affineEquiv_symm`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Convex_Alexandrov

variable {E : Type*}
variable [NormedAddCommGroup E]
variable [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem FunctionalInequalities.Analysis.subgradientImage_comp_affineEquiv_symm_readable (u : E → ℝ) (e : E ≃ᵃ[ℝ] E) (G : Set E) :
    subgradientImage (u ∘ e.symm) (e '' G) =
      (LinearMap.adjoint (e.linear.symm : E →ₗ[ℝ] E)) '' subgradientImage u G := by sorry
