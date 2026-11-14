-- Prove2me | Theorems.Thm_NarrowDNF_HatamiResidual_component_conditional_zero
-- name    : NarrowDNF.HatamiResidual.component_conditional_zero
-- status  : Proved
-- author  : @chenghua.liu
-- created : 2026-11-13T08:21:39.391211+00:00
-- url     : https://prove2.me/theorems/1792f71c-1a2c-494c-ae60-2cad60dd0b7b
-- title:
--   Fourier components have zero mean on incomplete coordinate fibers
-- statement:
--   Let $I$ be finite, $p\in\mathbb R$, $f:\{0,1\}^I\to\mathbb R$, and $S,T\subseteq I$ with $S\nsubseteq T$. For every assignment $z\in\{0,1\}^T$, the generalized biased Fourier component $F_S$ satisfies
--   $$\operatorname{mean}_{p,T}(F_S;z)=0.$$
--   The mean is defined as the product-weight sum of $F_S$ on the fiber $x|_T=z$ divided by that fiber's product-weight mass, using the total real division convention. The statement is algebraic for every real $p$; for $0<p<1$ it is ordinary conditional expectation.
-- source:
--   https://github.com/liuchliuch/narrow-dnf-lean/blob/eecadd6a5ea0a331d6cf9fd5cb39fc6ec854b372/NarrowDNF/HatamiResidual.lean#L537-L552

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Bool.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Real.Basic
import Mathlib.Logic.Equiv.Prod
import Mathlib.Order.Monotone.Basic
import Mathlib.Tactic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_NarrowDNF_Adaptive
import Definitions.Def_NarrowDNF_Certificates
import Definitions.Def_NarrowDNF_ConditionalExpectation
import Definitions.Def_NarrowDNF_CoordinateShift
import Definitions.Def_NarrowDNF_Fourier
import Definitions.Def_NarrowDNF_HatamiActivation
import Definitions.Def_NarrowDNF_HatamiResidual
import Definitions.Def_NarrowDNF_Influence
import Definitions.Def_NarrowDNF_LoadTransport
import Definitions.Def_NarrowDNF_ProductMeasure
import Theorems.Thm_NarrowDNF_HatamiResidual_coordinateMean_eq_of_local
import Theorems.Thm_NarrowDNF_ProductMeasure_expectation_split

namespace NarrowDNF
end NarrowDNF

namespace NarrowDNF.Activation
end NarrowDNF.Activation

namespace NarrowDNF.ConditionalExpectation
end NarrowDNF.ConditionalExpectation

namespace NarrowDNF.FiberShift
end NarrowDNF.FiberShift

namespace NarrowDNF.Fourier
end NarrowDNF.Fourier

namespace NarrowDNF.HatamiActivation
end NarrowDNF.HatamiActivation

namespace NarrowDNF.HatamiResidual
end NarrowDNF.HatamiResidual

namespace NarrowDNF.Influence
end NarrowDNF.Influence

namespace NarrowDNF.ProductMeasure
end NarrowDNF.ProductMeasure
noncomputable section
open scoped BigOperators
open NarrowDNF
open NarrowDNF.HatamiResidual
open ProductMeasure
attribute [local instance] Classical.propDecidable
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem NarrowDNF.HatamiResidual.component_conditional_zero (p : ℝ) (f : Cube ι → ℝ) (S T : Finset ι)
    (hST : ¬ S ⊆ T) (z : T → Bool) :
    ConditionalExpectation.mean (restriction T) (weight p) (Fourier.component p f S) z = 0 := by sorry
