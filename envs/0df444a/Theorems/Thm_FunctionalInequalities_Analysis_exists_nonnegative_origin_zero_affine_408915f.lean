-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_exists_nonnegative_origin_zero_affine_408915f
-- name    : FunctionalInequalities.Analysis.exists_nonnegative_origin_zero_affine_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:19:24.790998+00:00
-- url     : https://prove2.me/theorems/c6ff9d2a-5e5f-46ea-b980-227824086f4c
-- title:
--   Nonnegative Affine Normalization of a Convex Potential
-- statement:
--   This is a pointwise affine-normalization lemma supporting Proposition 12 of Cordero–Erausquin–Klartag (CorderoKlartag2015).
--
--   Let $E$ be finite-dimensional, let $f:E\to\overline{\mathbb R}$ be a `ConvexPotential`, and assume $0$ lies in the interior of its finite effective domain. Then there exists $a\in E$ such that, for $g=\operatorname{affineSubtract}(f,a,(f(0))_{\mathrm{toReal}})$, $g$ is a `ConvexPotential` and
--
--   $$0\le g(x)\quad\text{for every }x\in E,\qquad g(0)=0.$$
--
--   The conclusion concerns only pointwise normalization and does not involve measures or integrals.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Convex/Affine.lean#L122-L140 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Convex.Affine`, declaration `FunctionalInequalities.Analysis.exists_nonnegative_origin_zero_affine`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Affine
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Legendre
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Data.EReal.Operations
import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Topology.Semicontinuity.Basic

noncomputable section
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem FunctionalInequalities.Analysis.exists_nonnegative_origin_zero_affine_408915f [FiniteDimensional ℝ E]
    (f : E → EReal) (hf : ConvexPotential f)
    (h0 : (0 : E) ∈ interior {x | f x ≠ ⊤}) :
    ∃ a : E, let g := affineSubtract f a (f 0).toReal
      ConvexPotential g ∧ (∀ x, 0 ≤ g x) ∧ g 0 = 0 := by sorry
