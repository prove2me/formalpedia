-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_eventually_affineMaximum_sub_le_legendre_readable
-- name    : FunctionalInequalities.Analysis.eventually_affineMaximum_sub_le_legendre_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:04:06.776139+00:00
-- url     : https://prove2.me/theorems/5b6258b4-53ab-4ec0-9b82-126b22c2ab6c
-- title:
--   Eventual Affine-Maximum Lower Bound for Legendre Transforms
-- statement:
--   This formalizes equation (60) of Cordero-Erausquin–Klartag, *Moment measures* (arXiv:1304.0630v1).
--
--   Let $E$ be a real inner-product normed space, let $\phi_j:E\to\overline{\mathbb R}$ be a sequence of extended-real functions, and let $\psi:E\to\overline{\mathbb R}$. Let $s\subset E$ be a nonempty finite set. Assume every $\psi(x)$ for $x\in s$ is neither $+\infty$ nor $-\infty$, and that $\phi_j(x)\to\psi(x)$ at each $x\in s$. For $\varepsilon>0$, eventually in $j$ and for every $y\in E$,
--   $$\bigl(\operatorname{affineMaximum}(s,\psi_{|s}^{\mathrm{toReal}},y)-\varepsilon\bigr)
--   \le (\phi_j)^*(y),$$
--   where the left side is embedded into `EReal` and $(\phi_j)^*$ is `legendre (φ j)`.
--
--   The statement provides a bound uniform in the dual point $y$, obtained from pointwise convergence at finitely many vertices. It is a geometric approximation tool for Legendre transforms.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem eventually_affineMaximum_sub_le_legendre
--       (φ : ℕ → E → EReal) (ψ : E → EReal) (s : Finset E) (hs : s.Nonempty)
--       (hfin : ∀ x ∈ s, ψ x ≠ ⊤ ∧ ψ x ≠ ⊥)
--       (hlim : ∀ x ∈ s, Tendsto (fun j => φ j x) atTop (𝓝 (ψ x)))
--       {ε : ℝ} (hε : 0 < ε) :
--       ∀ᶠ j in atTop, ∀ y : E,
--         ((affineMaximum s hs (fun x => (ψ x).toReal) y - ε : ℝ) : EReal) ≤
--           legendre (φ j) y
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/Convex/AffineMaximum`](https://prove2.me/theorems/6ce50813-8eec-46a5-abb0-e806e1385307).
--
--   Definition modules: [`Analysis/Convex/Legendre`](https://prove2.me/theorems/ccf34d51-1332-4642-a3a3-dacdd0cbab81).
--
--   Previous: [`affineMaximum_coercive`](https://prove2.me/theorems/e32066d6-367b-466d-9089-f5d72ac05f70).
--
--   [Source excerpt, lines 102–109](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Convex/AffineMaximum.lean#L102-L109) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Convex/AffineMaximum.lean#L100-L131 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Convex.AffineMaximum`, declaration `FunctionalInequalities.Analysis.eventually_affineMaximum_sub_le_legendre`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Convex_AffineMaximum

open Filter Set
open scoped Topology
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem FunctionalInequalities.Analysis.eventually_affineMaximum_sub_le_legendre_readable
    (φ : ℕ → E → EReal) (ψ : E → EReal) (s : Finset E) (hs : s.Nonempty)
    (hfin : ∀ x ∈ s, ψ x ≠ ⊤ ∧ ψ x ≠ ⊥)
    (hlim : ∀ x ∈ s, Tendsto (fun j => φ j x) atTop (𝓝 (ψ x)))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ j in atTop, ∀ y : E,
      ((affineMaximum s hs (fun x => (ψ x).toReal) y - ε : ℝ) : EReal) ≤
        legendre (φ j) y := by sorry
