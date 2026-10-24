-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_convex_epigraph_affineSubtract_408915f
-- name    : FunctionalInequalities.Analysis.convex_epigraph_affineSubtract_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:16:39.115567+00:00
-- url     : https://prove2.me/theorems/0538f5b7-8725-4ec7-b7b8-0607888f481c
-- title:
--   Affine Subtraction Preserves Epigraph Convexity
-- statement:
--   This proves preservation of real epigraph convexity under affine subtraction.
--
--   Let $E$ be a real inner-product space, let $f:E\to\overline{\mathbb R}$, let $a\in E$, and let $b\in\mathbb R$. Assume the real epigraph
--   $$\{(p,r)\in E\times\mathbb R:f(p)\le r\}$$
--   is convex. Define `affineSubtract` by
--   $$\operatorname{affineSubtract}(f,a,b)(x)=f(x)-\bigl(\langle a,x\rangle+b\bigr).$$
--   Then its real epigraph is convex:
--   $$\{(p,r):\operatorname{affineSubtract}(f,a,b)(p)\le r\}\text{ is convex}.$$
--
--   This is measure-free infrastructure for affine normalization of extended-real convex potentials.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Convex/Affine.lean#L90-L121 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Convex.Affine`, declaration `FunctionalInequalities.Analysis.convex_epigraph_affineSubtract`; the repository is private at upload time).

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

theorem FunctionalInequalities.Analysis.convex_epigraph_affineSubtract_408915f (f : E → EReal) (a : E) (b : ℝ)
    (hf : Convex ℝ {p : E × ℝ | f p.1 ≤ (p.2 : EReal)}) :
    Convex ℝ {p : E × ℝ | affineSubtract f a b p.1 ≤ (p.2 : EReal)} := by sorry
