-- Prove2me | Theorems.Thm_FunctionalInequalities_Probability_MomentMeasure_limsup_density_legendre_le_readable
-- name    : FunctionalInequalities.Probability.MomentMeasure.limsup_density_legendre_le_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:05:00.458566+00:00
-- url     : https://prove2.me/theorems/50c36fd7-1bb7-40be-8a5b-91f04f40fa30
-- title:
--   Pointwise Limsup Bound For Legendre Densities
-- statement:
--   This is the pointwise density component of the upper semicontinuity statement associated with Lemma 17 of Cordero–Erausquin–Klartag, *Moment measures* (arXiv:1304.0630v1), cited there as a partial formalization.
--
--   Let $E$ be a real-inner-product normed additive group, let $\phi_j:E\to\overline{\mathbb R}$, let $\psi:E\to\overline{\mathbb R}$, and let $K\subseteq E$. Assume:
--
--   1. For every $x\in K$, $\phi_j(x)\to\psi(x)$.
--   2. For every $y\in E$,
--      $$\psi^*(y)=\sup_{x\in K}\bigl(\langle x,y\rangle-\psi(x)\bigr).$$
--
--   Then, for every $y\in E$,
--   $$\limsup_{j\to\infty}\operatorname{density}(\phi_j^*)(y)\le\operatorname{density}(\psi^*)(y).$$
--
--   The result allows extended-real conjugate values and density values in $[0,\infty]$.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Probability.MomentMeasure`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem limsup_density_legendre_le
--       (φ : ℕ → E → EReal) (ψ : E → EReal) {K : Set E}
--       (hlim : ∀ x ∈ K, Tendsto (fun j => φ j x) atTop (𝓝 (ψ x)))
--       (hsup : ∀ y, legendre ψ y = ⨆ x ∈ K, (inner ℝ x y : EReal) - ψ x)
--       (y : E) :
--       limsup (fun j => density (legendre (φ j)) y) atTop ≤ density (legendre ψ) y
--   ```
--
--   **Module navigation**
--
--   Module: [`Probability/MomentMeasure/ConjugateMass`](https://prove2.me/theorems/c85f19a1-3736-404d-9ea6-0652c177907f).
--
--   Definition modules: [`Probability/MomentMeasure/Basic`](https://prove2.me/theorems/c1dff218-c76c-41e5-85d4-6f51771cc46c), [`Analysis/Convex/Legendre`](https://prove2.me/theorems/ccf34d51-1332-4642-a3a3-dacdd0cbab81).
--
--   Previous: [`integrable_exp_sub_norm`](https://prove2.me/theorems/6e84bf56-c441-4d85-881f-7cdd5b15ecb5) · Next: [`exists_integrable_exponential_domination`](https://prove2.me/theorems/0002089c-2c4b-4c6b-8010-16b85c45339e).
--
--   [Source excerpt, lines 69–74](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Probability/MomentMeasure/ConjugateMass.lean#L69-L74) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Probability/MomentMeasure/ConjugateMass.lean#L66-L102 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Probability.MomentMeasure.ConjugateMass`, declaration `FunctionalInequalities.Probability.MomentMeasure.limsup_density_legendre_le`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Probability_MomentMeasure_ConjugateMass

open MeasureTheory Filter Set
open scoped ENNReal Topology
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
open FunctionalInequalities.Analysis

theorem FunctionalInequalities.Probability.MomentMeasure.limsup_density_legendre_le_readable
    (φ : ℕ → E → EReal) (ψ : E → EReal) {K : Set E}
    (hlim : ∀ x ∈ K, Tendsto (fun j => φ j x) atTop (𝓝 (ψ x)))
    (hsup : ∀ y, legendre ψ y = ⨆ x ∈ K, (inner ℝ x y : EReal) - ψ x)
    (y : E) :
    limsup (fun j => density (legendre (φ j)) y) atTop ≤ density (legendre ψ) y := by sorry
