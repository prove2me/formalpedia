-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_legendre_eq_interior_sup_408915f
-- name    : FunctionalInequalities.Analysis.legendre_eq_interior_sup_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:21:34.613447+00:00
-- url     : https://prove2.me/theorems/d6a90bab-e4f3-4756-ab62-debeed0938d5
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
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Convex/Legendre.lean#L252-L293 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Convex.Legendre`, declaration `FunctionalInequalities.Analysis.legendre_eq_interior_sup`; the repository is private at upload time).

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
section RadialClosure
open Filter Set
open scoped Topology

theorem FunctionalInequalities.Analysis.legendre_eq_interior_sup_408915f
    {K : Set E} (hK : IsOpen K) (hKconv : Convex ℝ K) (h0 : (0 : E) ∈ K)
    (ψ : E → EReal)
    (hrad : ∀ x, Tendsto (fun t : ℝ => ψ (t • x)) (𝓝[<] 1) (𝓝 (ψ x)))
    (hoff : ∀ x ∉ closure K, ψ x = ⊤) (y : E) :
    legendre ψ y = ⨆ x ∈ K, (inner ℝ x y : EReal) - ψ x := by sorry
