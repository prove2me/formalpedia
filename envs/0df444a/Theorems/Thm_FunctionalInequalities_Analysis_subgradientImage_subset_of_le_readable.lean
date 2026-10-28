-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_subgradientImage_subset_of_le_readable
-- name    : FunctionalInequalities.Analysis.subgradientImage_subset_of_le_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:04:01.160576+00:00
-- url     : https://prove2.me/theorems/48dd6fd6-70dd-48c0-b715-081cfd732396
-- title:
--   Monotonicity of Subgradient Images
-- statement:
--   This formalizes the comparison principle stated as Lemma 1.4.1 of Gutiérrez, *The Monge–Ampère equation*.
--
--   Let $E$ be a finite-dimensional real inner-product normed space, and let $u,v:E\to\mathbb R$ be convex on all of $E$. Let $\Omega\subseteq E$ be open and bounded. Assume:
--
--   1. $u(x)\le v(x)$ for every $x\in\Omega$;
--   2. $u(x)=v(x)$ for every $x\in\partial\Omega$.
--
--   Writing `subgradientImage` for the set of vectors that are subgradients at points of a set, the conclusion is
--   $$\operatorname{subgradientImage}(v,\Omega)\subseteq \operatorname{subgradientImage}(u,\Omega).$$
--
--   This is a finite-dimensional comparison result for convex subgradient images and is reusable in Alexandrov- and Monge–Ampère-type arguments.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem subgradientImage_subset_of_le
--       [FiniteDimensional ℝ E] {u v : E → ℝ} (hu : ConvexOn ℝ univ u) (hv : ConvexOn ℝ univ v)
--       {Ω : Set E} (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) (hle : ∀ x ∈ Ω, u x ≤ v x)
--       (heq : ∀ x ∈ frontier Ω, u x = v x) : subgradientImage v Ω ⊆ subgradientImage u Ω
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/Convex/Subgradient`](https://prove2.me/theorems/67a77afb-a546-4173-875a-237133f9cad7).
--
--   Supporting theorems: [`support_of_max`](https://prove2.me/theorems/755fde81-3294-4941-84e6-f374b8550b71).
--
--   Previous: [`support_of_max`](https://prove2.me/theorems/755fde81-3294-4941-84e6-f374b8550b71) · Next: [`volume_subgradient_two_points_eq_zero`](https://prove2.me/theorems/097fae72-0e02-4d52-bbb1-f4883ba49bd8).
--
--   [Source excerpt, lines 992–995](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Convex/Subgradient.lean#L992-L995) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Convex/Subgradient.lean#L989-L1045 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Convex.Subgradient`, declaration `FunctionalInequalities.Analysis.subgradientImage_subset_of_le`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Convex_Subgradient

open Set
variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem FunctionalInequalities.Analysis.subgradientImage_subset_of_le_readable
    [FiniteDimensional ℝ E] {u v : E → ℝ} (hu : ConvexOn ℝ univ u) (hv : ConvexOn ℝ univ v)
    {Ω : Set E} (hΩ : IsOpen Ω) (hb : Bornology.IsBounded Ω) (hle : ∀ x ∈ Ω, u x ≤ v x)
    (heq : ∀ x ∈ frontier Ω, u x = v x) : subgradientImage v Ω ⊆ subgradientImage u Ω := by sorry
