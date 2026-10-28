-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_directional_bilinear_readable
-- name    : FunctionalInequalities.Analysis.directional_bilinear_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:02:01.952142+00:00
-- url     : https://prove2.me/theorems/c7268247-0081-4a71-b098-d28d94f91226
-- title:
--   Higher Leibniz Rule for Bilinear Images
-- statement:
--   This is the raw higher-order Leibniz rule for a continuous bilinear map.
--
--   Let $E,F,G,H$ be real normed spaces, let $B:F\to(G\to H)$ be a continuous bilinear map, and let $f:E\to F$ and $g:E\to G$ be $C^\infty$. For $m\in\mathbb N$, directions $h_0,\ldots,h_{m-1}\in E$, and $x\in E$,
--
--   $$D^m\bigl(y\mapsto B(f(y),g(y))\bigr)(x)[h_0,\ldots,h_{m-1}]$$
--   $$=\sum_{q:\operatorname{Fin}(m)\to\{\mathrm{false},\mathrm{true}\}} B\bigl(D^{|q|}f(x)[h_j:q(j)=\mathrm{true}],D^{m-|q|}g(x)[h_j:q(j)=\mathrm{false}]\bigr).$$
--
--   The selected directions retain their inherited order, and every Boolean allocation appears with coefficient one. This is generic calculus support for expansions of quadratic and bilinear expressions.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Analysis`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem directional_bilinear (B : F →L[ℝ] G →L[ℝ] H)
--       {f : E → F} {g : E → G} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
--       (m : ℕ) (h : Fin m → E) (x : E) :
--       directional (List.ofFn h) (fun y => B (f y) (g y)) x =
--         ∑ q : Fin m → Bool,
--           B (directional (selected h q) f x)
--             (directional (selected h (fun i => !(q i))) g x)
--   ```
--
--   **Module navigation**
--
--   Module: [`Analysis/IteratedDerivative/Bilinear`](https://prove2.me/theorems/c2e12327-8e36-4fb7-a6f8-00519f39d229).
--
--   Definition modules: [`Analysis/IteratedDerivative/Symmetry`](https://prove2.me/theorems/c3281ab2-65ad-4ae5-995a-70d685aba1dc).
--
--   Next: [`sum_filter_eq_two_mul_sum_filter_of_compl_invariant`](https://prove2.me/theorems/df0e8f70-61ce-476e-a922-0def8bd9c052).
--
--   [Source excerpt, lines 54–60](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Analysis/IteratedDerivative/Bilinear.lean#L54-L60) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/IteratedDerivative/Bilinear.lean#L52-L86 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.IteratedDerivative.Bilinear`, declaration `FunctionalInequalities.Analysis.directional_bilinear`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_IteratedDerivative_Bilinear

open scoped ContDiff
variable {E F G H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup H] [NormedSpace ℝ H]

theorem FunctionalInequalities.Analysis.directional_bilinear_readable (B : F →L[ℝ] G →L[ℝ] H)
    {f : E → F} {g : E → G} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (m : ℕ) (h : Fin m → E) (x : E) :
    directional (List.ofFn h) (fun y => B (f y) (g y)) x =
      ∑ q : Fin m → Bool,
        B (directional (selected h q) f x)
          (directional (selected h (fun i => !(q i))) g x) := by sorry
