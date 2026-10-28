-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_subgradientImage_sub_inner_add_const_readable
-- name    : FunctionalInequalities.Analysis.subgradientImage_sub_inner_add_const_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:04:01.283996+00:00
-- url     : https://prove2.me/theorems/8b64958d-7cd7-4f0c-96e8-9c9b1e0139d2
-- title:
--   Affine Subtraction Translates Subgradient Images
-- statement:
--   This identifies the effect of subtracting an affine function on subgradient images.
--
--   Let $E$ be a real inner-product space, let $u:E\to\mathbb R$, $p\in E$, $c\in\mathbb R$, and $G\subseteq E$. Then, using `subgradientImage`,
--   $$\partial\bigl(u-\langle p,\cdot\rangle-c\bigr)(G)=\{q-p:q\in\partial u(G)\}.$$
--   Equivalently, the subgradient image is translated by $-p$.
--
--   This is a bookkeeping identity used to transfer volume estimates under affine normalization.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem subgradientImage_sub_inner_add_const (u : E → ℝ) (p : E) (c : ℝ) (G : Set E) :
--       subgradientImage (fun x => u x - (⟪p, x⟫ + c)) G = (fun q => q - p) '' subgradientImage u G
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/Convex/Alexandrov`](https://prove2.me/theorems/3d12d62d-28ee-413a-8964-1771fdfa5905).
--
--   Definition modules: [`Analysis/Convex/Subgradient`](https://prove2.me/theorems/67a77afb-a546-4173-875a-237133f9cad7).
--
--   Previous: [`volume_subgradientImage_comp_affineEquiv_symm`](https://prove2.me/theorems/17cd1bb9-8c78-49af-a2a8-52c8ebcc13dc) · Next: [`volume_subgradientImage_eq_lintegral_of_isOpen`](https://prove2.me/theorems/a875c8d6-d13c-4184-b1ba-d8541c085171).
--
--   [Source excerpt, lines 2118–2119](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Convex/Alexandrov.lean#L2118-L2119) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Convex/Alexandrov.lean#L2117-L2136 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Convex.Alexandrov`, declaration `FunctionalInequalities.Analysis.subgradientImage_sub_inner_add_const`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Convex_Alexandrov

open scoped RealInnerProductSpace
variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem FunctionalInequalities.Analysis.subgradientImage_sub_inner_add_const_readable (u : E → ℝ) (p : E) (c : ℝ) (G : Set E) :
    subgradientImage (fun x => u x - (⟪p, x⟫ + c)) G = (fun q => q - p) '' subgradientImage u G := by sorry
