-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_convex_epigraph_legendre_408915f
-- name    : FunctionalInequalities.Analysis.convex_epigraph_legendre_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:14:50.879786+00:00
-- url     : https://prove2.me/theorems/699be76a-1f08-444b-96ac-ef503ba0165c
-- title:
--   Convexity of the Real Legendre Epigraph
-- statement:
--   This proves convexity of the real epigraph of the Legendre transform.
--
--   Let $E$ be a real inner-product space and let $\varphi:E\to\overline{\mathbb R}$ be arbitrary, with `EReal` allowing the values $\pm\infty$. Define the Legendre transform by `legendre`. Then
--   $$\left\{(p,r)\in E\times\mathbb R:\operatorname{legendre}(\varphi)(p)\le r\right\}$$
--   is convex.
--
--   The statement is measure-free and applies without convexity, properness, or finiteness assumptions on $\varphi$. It is basic infrastructure for later properties of conjugates and biconjugates.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Convex/Legendre.lean#L149-L178 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Convex.Legendre`, declaration `FunctionalInequalities.Analysis.convex_epigraph_legendre`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Legendre
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.InnerProductSpace.Continuous
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
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem FunctionalInequalities.Analysis.convex_epigraph_legendre_408915f (φ : E → EReal) :
    Convex ℝ {p : E × ℝ | legendre φ p.1 ≤ (p.2 : EReal)} := by sorry
