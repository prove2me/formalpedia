-- Prove2me | Theorems.Thm_NarrowDNF_HatamiResidual_sum_diagonal_le_small_mass
-- name    : NarrowDNF.HatamiResidual.sum_diagonal_le_small_mass
-- status  : Proved
-- author  : @chenghua.liu
-- created : 2026-11-13T08:24:57.457214+00:00
-- url     : https://prove2.me/theorems/82f9554c-a396-461e-a7ef-78c307e68132
-- title:
--   Diagonal conditional-approximation error is bounded by low-degree small-component mass
-- statement:
--   Let $I$ be finite, $0<p<1$, $\delta\le1$, and $k,\eta\in\mathbb R$. For a real function $f$, write $F_S$ for its biased Walsh component and $R=\{S:|S|\le k,\ \max_x|F_S(x)|>\eta\}$. Define $b_T=\sum_{S\in R,T\subseteq S}\Pr_p(|F_S|\ge\eta)$; the activation $J$ fires on $T$ when $|T|\le k$ and $\delta\mu_{p,T}(x_T)\le b_T$. Let $\widetilde F_S$ be conditional expectation of $F_S$ onto the adaptive partition retaining only activations indexed inside $S$. Then
--   $$
--   \sum_{S\in R}\mathbb E_p[(F_S-\widetilde F_S)^2]
--   \le\mathbb E_p\sum_{|S|\le k}\mathbf1_{\{|F_S|\le\eta\}}F_S^2.
--   $$
--   This isolates the diagonal part of the residual estimate.
-- source:
--   https://github.com/liuchliuch/narrow-dnf-lean/blob/eecadd6a5ea0a331d6cf9fd5cb39fc6ec854b372/NarrowDNF/HatamiResidual.lean#L368-L393

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
import Theorems.Thm_NarrowDNF_ConditionalExpectation_adaptiveCode_eq_iff
import Theorems.Thm_NarrowDNF_ConditionalExpectation_squaredError_decomposition
import Theorems.Thm_NarrowDNF_HatamiActivation_localMass_le_componentTailMass
import Theorems.Thm_NarrowDNF_HatamiResidual_fires_congr_atom

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

theorem NarrowDNF.HatamiResidual.sum_diagonal_le_small_mass {p k δ η : ℝ}
    (hp0 : 0 < p) (hp1 : p < 1) (hδ : δ ≤ 1) (f : Cube ι → ℝ) :
    (∑ S ∈ HatamiActivation.significantSets p f k η,
      ConditionalExpectation.squaredError (weight p) (Fourier.component p f S)
        (approxComponent p (HatamiActivation.fourierActivation k p δ η f) f S)) ≤
      expectation p (fun x =>
        ∑ S ∈ Finset.univ.filter (fun S : Finset ι => (S.card : ℝ) ≤ k),
          if |Fourier.component p f S x| ≤ η then Fourier.component p f S x ^ 2 else 0) := by sorry
