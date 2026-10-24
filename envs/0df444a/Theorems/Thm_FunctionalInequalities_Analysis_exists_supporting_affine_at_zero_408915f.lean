-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_exists_supporting_affine_at_zero_408915f
-- name    : FunctionalInequalities.Analysis.exists_supporting_affine_at_zero_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:19:25.461034+00:00
-- url     : https://prove2.me/theorems/04bf8d8f-d7dc-417b-9b77-3bab0e867914
-- title:
--   Supporting Affine Minorant at the Origin
-- statement:
--   This formalizes a stronger pointwise supporting-plane statement related to Proposition 12 of Cordero–Erausquin–Klartag (CorderoKlartag2015).
--
--   Let $E$ be finite-dimensional, let $f:E\to\overline{\mathbb R}$ be a `ConvexPotential`, and assume $0$ lies in the interior of $\{x:f(x)\ne+\infty\}$. Then there exists $a\in E$ such that, for every $x\in E$,
--
--   $$\langle a,x\rangle+(f(0))_{\mathrm{toReal}}\le f(x),$$
--
--   where the affine expression is embedded into the extended reals. This is a pointwise supporting affine minorant and is not the variational maximizer assertion of the cited proposition.
-- source:
--   Source: Cordero-Erausquin–Klartag, Moment measures (arXiv:1304.0630v1), Proposition 12. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Convex/SupportingPlane.lean#L74-L183 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Convex.SupportingPlane`, declaration `FunctionalInequalities.Analysis.exists_supporting_affine_at_zero`; the repository is private at upload time).

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

theorem FunctionalInequalities.Analysis.exists_supporting_affine_at_zero_408915f [FiniteDimensional ℝ E]
    (f : E → EReal) (hf : ConvexPotential f)
    (h0 : (0 : E) ∈ interior {x | f x ≠ ⊤}) :
    ∃ a : E, ∀ x, ((inner ℝ a x + (f 0).toReal : ℝ) : EReal) ≤ f x := by sorry
