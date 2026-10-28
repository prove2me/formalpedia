-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_support_of_max_readable
-- name    : FunctionalInequalities.Analysis.support_of_max_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:03:56.314897+00:00
-- url     : https://prove2.me/theorems/755fde81-3294-4941-84e6-f374b8550b71
-- title:
--   Supporting Hyperplane From an Interior Maximum
-- statement:
--   This is a technical supporting-hyperplane lemma for a convex function.
--
--   Let $E$ be a real inner-product normed additive group, let $u:E\to\mathbb R$ be convex on all of $E$, and let $\Omega\subseteq E$ be open. For $x_0,x_1,p\in E$ and $c\in\mathbb R$, assume $x_1\in\Omega$ and that $x_1$ maximizes
--   $$z\mapsto c+\langle p,z-x_0\rangle-u(z)$$
--   on over $\overline\Omega$. Then, for every $y\in E$,
--   $$u(x_1)+\langle p,y-x_1\rangle\le u(y).$$
--
--   The result identifies $p$ as a subgradient of $u$ at $x_1$, using the inline subgradient formulation rather than a separate subdifferential object. It is used to convert a maximizer of an affine perturbation into a global supporting inequality.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   private lemma support_of_max
--       {u : E → ℝ} {Ω : Set E} (hu : ConvexOn ℝ univ u) (hΩ : IsOpen Ω)
--       (x₀ x₁ p : E) (c : ℝ) (hx₁ : x₁ ∈ Ω)
--       (hmax :
--         IsMaxOn (fun z => c + ⟪p, z - x₀⟫ - u z) (closure Ω) x₁) :
--       ∀ y, u x₁ + ⟪p, y - x₁⟫ ≤ u y
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/Convex/Subgradient`](https://prove2.me/theorems/67a77afb-a546-4173-875a-237133f9cad7).
--
--   Previous: [`hasFDerivAt_of_convexOn_of_unique_subgradient`](https://prove2.me/theorems/690ed838-72ba-4da4-b243-c587f4147186) · Next: [`subgradientImage_subset_of_le`](https://prove2.me/theorems/48dd6fd6-70dd-48c0-b715-081cfd732396).
--
--   [Source excerpt, lines 870–875](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Convex/Subgradient.lean#L870-L875) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Convex/Subgradient.lean#L870-L981 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Convex.Subgradient`, declaration `_private.FunctionalInequalities.Analysis.Convex.Subgradient.0.FunctionalInequalities.Analysis.support_of_max`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Convex_Subgradient

open scoped RealInnerProductSpace
open Set
variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]

lemma FunctionalInequalities.Analysis.support_of_max_readable
    {u : E → ℝ} {Ω : Set E} (hu : ConvexOn ℝ univ u) (hΩ : IsOpen Ω)
    (x₀ x₁ p : E) (c : ℝ) (hx₁ : x₁ ∈ Ω)
    (hmax :
      IsMaxOn (fun z => c + ⟪p, z - x₀⟫ - u z) (closure Ω) x₁) :
    ∀ y, u x₁ + ⟪p, y - x₁⟫ ≤ u y := by sorry
