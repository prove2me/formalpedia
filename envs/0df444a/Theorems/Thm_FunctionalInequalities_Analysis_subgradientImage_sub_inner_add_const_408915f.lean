-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_subgradientImage_sub_inner_add_const_408915f
-- name    : FunctionalInequalities.Analysis.subgradientImage_sub_inner_add_const_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:15:00.157149+00:00
-- url     : https://prove2.me/theorems/41d2cdaf-b739-45ce-8687-a2593c23c12e
-- title:
--   Affine Subtraction Translates Subgradient Images
-- statement:
--   This identifies the effect of subtracting an affine function on subgradient images.
--
--   Let $E$ be a real inner-product space, let $u:E\to\mathbb R$, $p\in E$, $c\in\mathbb R$, and $G\subseteq E$. Then, using `subgradientImage`,
--   $$\partial\bigl(u-\langle p,\cdot\rangle-c\bigr)(G)=\{q-p:q\in\partial u(G)\}.$$
--   Equivalently, the subgradient image is translated by $-p$.
--
--   This is a bookkeeping identity used to transfer volume estimates under affine normalization.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Convex/Alexandrov.lean#L2117-L2136 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Convex.Alexandrov`, declaration `FunctionalInequalities.Analysis.subgradientImage_sub_inner_add_const`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_AffineMaximum
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Alexandrov
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Legendre
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Subgradient
import Mathlib
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Measure
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Normed.Affine.Convex
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Data.EReal.Operations
import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Topology.Semicontinuity.Basic

noncomputable section
open MeasureTheory Set
open scoped RealInnerProductSpace ENNReal
section LT11E6SubgradientimageSubAffine
open MeasureTheory Set
open scoped RealInnerProductSpace
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
section InnerProduct
variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem FunctionalInequalities.Analysis.subgradientImage_sub_inner_add_const_408915f (u : E → ℝ) (p : E) (c : ℝ) (G : Set E) :
    subgradientImage (fun x => u x - (⟪p, x⟫ + c)) G = (fun q => q - p) '' subgradientImage u G := by sorry
