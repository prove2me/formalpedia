-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_directional_bilinear_408915f
-- name    : FunctionalInequalities.Analysis.directional_bilinear_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:04:32.553544+00:00
-- url     : https://prove2.me/theorems/e5254a60-91be-4900-989c-5979a9083787
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
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/IteratedDerivative/Bilinear.lean#L52-L86 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.IteratedDerivative.Bilinear`, declaration `FunctionalInequalities.Analysis.directional_bilinear`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_IteratedDerivative_Bilinear
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_IteratedDerivative_Symmetry
import Mathlib.Algebra.BigOperators.Group.Finset.Pi
import Mathlib.Analysis.Calculus.FDeriv.Bilinear
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Data.List.FinRange

noncomputable section
open scoped ContDiff
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
variable {E F G H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup H] [NormedSpace ℝ H]

theorem FunctionalInequalities.Analysis.directional_bilinear_408915f (B : F →L[ℝ] G →L[ℝ] H)
    {f : E → F} {g : E → G} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (m : ℕ) (h : Fin m → E) (x : E) :
    directional (List.ofFn h) (fun y => B (f y) (g y)) x =
      ∑ q : Fin m → Bool,
        B (directional (selected h q) f x)
          (directional (selected h (fun i => !(q i))) g x) := by sorry
