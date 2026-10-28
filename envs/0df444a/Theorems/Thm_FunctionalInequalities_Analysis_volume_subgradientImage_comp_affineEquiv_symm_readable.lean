-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_volume_subgradientImage_comp_affineEquiv_symm_readable
-- name    : FunctionalInequalities.Analysis.volume_subgradientImage_comp_affineEquiv_symm_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:03:41.686449+00:00
-- url     : https://prove2.me/theorems/17cd1bb9-8c78-49af-a2a8-52c8ebcc13dc
-- title:
--   Volume Scaling of Transported Subgradient Images
-- statement:
--   This gives the volume-scaling version of affine transport for subgradient images.
--
--   Let $E$ be a finite-dimensional real inner-product space with measurable and Borel structures, let $u:E\to\mathbb R$, let $e:E\simeq_A E$, and let $G\subseteq E$. Writing $T=e.linear$, one has
--
--   $$
--   \operatorname{vol}\big(\operatorname{subgradientImage}(u\circ e^{-1},e(G))\big)
--   =\operatorname{ofReal}\!\left(|\det T|^{-1}\right)\operatorname{vol}\big(\operatorname{subgradientImage}(u,G)\big).
--   $$
--
--   The volume values lie in $[0,\infty]$ (`ENNReal`), while the determinant factor is embedded with `ofReal`. The declaration is `volume_subgradientImage_comp_affineEquiv_symm_readable`; no finiteness of either measured set is assumed.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem volume_subgradientImage_comp_affineEquiv_symm [MeasurableSpace E] [BorelSpace E]
--       (u : E → ℝ) (e : E ≃ᵃ[ℝ] E) (G : Set E) :
--       (volume : Measure E) (subgradientImage (u ∘ e.symm) (e '' G)) =
--         ENNReal.ofReal |LinearMap.det (e.linear : E →ₗ[ℝ] E)|⁻¹ *
--           (volume : Measure E) (subgradientImage u G)
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/Convex/Alexandrov`](https://prove2.me/theorems/3d12d62d-28ee-413a-8964-1771fdfa5905).
--
--   Definition modules: [`Analysis/Convex/Subgradient`](https://prove2.me/theorems/67a77afb-a546-4173-875a-237133f9cad7).
--
--   Supporting theorems: [`subgradientImage_comp_affineEquiv_symm`](https://prove2.me/theorems/3ad116ee-9145-4587-a1b0-81a8f51d65df).
--
--   Previous: [`subgradientImage_comp_affineEquiv_symm`](https://prove2.me/theorems/3ad116ee-9145-4587-a1b0-81a8f51d65df) · Next: [`subgradientImage_sub_inner_add_const`](https://prove2.me/theorems/8b64958d-7cd7-4f0c-96e8-9c9b1e0139d2).
--
--   [Source excerpt, lines 1859–1863](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Convex/Alexandrov.lean#L1859-L1863) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Convex/Alexandrov.lean#L1858-L1939 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Convex.Alexandrov`, declaration `FunctionalInequalities.Analysis.volume_subgradientImage_comp_affineEquiv_symm`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Convex_Alexandrov

open MeasureTheory Set
variable {E : Type*}
variable [NormedAddCommGroup E]
variable [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem FunctionalInequalities.Analysis.volume_subgradientImage_comp_affineEquiv_symm_readable [MeasurableSpace E] [BorelSpace E]
    (u : E → ℝ) (e : E ≃ᵃ[ℝ] E) (G : Set E) :
    (volume : Measure E) (subgradientImage (u ∘ e.symm) (e '' G)) =
      ENNReal.ofReal |LinearMap.det (e.linear : E →ₗ[ℝ] E)|⁻¹ *
        (volume : Measure E) (subgradientImage u G) := by sorry
