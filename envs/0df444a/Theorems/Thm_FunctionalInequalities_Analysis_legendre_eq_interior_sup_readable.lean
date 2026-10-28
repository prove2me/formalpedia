-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_legendre_eq_interior_sup_readable
-- name    : FunctionalInequalities.Analysis.legendre_eq_interior_sup_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:05:17.652768+00:00
-- url     : https://prove2.me/theorems/fb27a67d-8a39-4dbc-904c-e8977c7bb3af
-- title:
--   Legendre Transform As A Supremum Over An Open Convex Set
-- statement:
--   This is a measure-free representation formula for the Legendre transform.
--
--   Let $E$ be a real inner-product normed additive group and let $K\subseteq E$ be open and convex with $0\in K$. Let $\psi:E\to\overline{\mathbb R}$ satisfy:
--
--   1. For every $x\in E$, $\psi(tx)\to\psi(x)$ as $t\to1$ from below.
--   2. If $x\notin\overline K$, then $\psi(x)=+\infty$.
--
--   Then, for every $y\in E$,
--   $$\psi^*(y)=\sup_{x\in K}\bigl(\langle x,y\rangle-\psi(x)\bigr).$$
--
--   The formula identifies the full Legendre transform with the supremum of affine terms restricted to the original open set.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem legendre_eq_interior_sup
--       {K : Set E} (hK : IsOpen K) (hKconv : Convex ℝ K) (h0 : (0 : E) ∈ K)
--       (ψ : E → EReal)
--       (hrad : ∀ x, Tendsto (fun t : ℝ => ψ (t • x)) (𝓝[<] 1) (𝓝 (ψ x)))
--       (hoff : ∀ x ∉ closure K, ψ x = ⊤) (y : E) :
--       legendre ψ y = ⨆ x ∈ K, (inner ℝ x y : EReal) - ψ x
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/Convex/Legendre`](https://prove2.me/theorems/ccf34d51-1332-4642-a3a3-dacdd0cbab81).
--
--   Previous: [`lowerTruncate_convexification`](https://prove2.me/theorems/1d40fba2-adb7-47d5-9def-9ed116ba3cc6) · Next: [`legendre_norm`](https://prove2.me/theorems/7eb3b3f3-e05d-4ad0-a70e-b08de926b3ea).
--
--   [Source excerpt, lines 255–260](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/Convex/Legendre.lean#L255-L260) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Convex/Legendre.lean#L252-L293 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Convex.Legendre`, declaration `FunctionalInequalities.Analysis.legendre_eq_interior_sup`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Convex_Legendre

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
open Filter Set
open scoped Topology

theorem FunctionalInequalities.Analysis.legendre_eq_interior_sup_readable
    {K : Set E} (hK : IsOpen K) (hKconv : Convex ℝ K) (h0 : (0 : E) ∈ K)
    (ψ : E → EReal)
    (hrad : ∀ x, Tendsto (fun t : ℝ => ψ (t • x)) (𝓝[<] 1) (𝓝 (ψ x)))
    (hoff : ∀ x ∉ closure K, ψ x = ⊤) (y : E) :
    legendre ψ y = ⨆ x ∈ K, (inner ℝ x y : EReal) - ψ x := by sorry
