-- Prove2me | Theorems.Thm_NarrowDNF_BourgainSquareFunction_low_degree_le_damped
-- name    : NarrowDNF.BourgainSquareFunction.low_degree_le_damped
-- status  : Proved
-- author  : @chenghua.liu
-- created : 2026-11-13T08:10:46.960612+00:00
-- url     : https://prove2.me/theorems/f1e08773-d582-4832-8056-0f0b28bdead1
-- title:
--   Low-degree energy is controlled by geometrically damped energy
-- statement:
--   Let \(I\) be a finite coordinate set and let \(a_S\in\mathbb R\) be an arbitrary array indexed by subsets \(S\subseteq I\). For any nonnegative integers \(k,m\),
--   $$\sum_{|S|\le k}a_S^2\le3^{mk}\sum_{S\subseteq I}\frac{a_S^2}{3^{m|S|}}.$$
--   Subset indices correspond exactly to the Boolean support masks used in the formal statement, and their degree is \(|S|\). The inequality converts a low-degree truncation into a full spectral sum with geometric damping. It requires no probability measure or assumption that the array consists of Fourier coefficients.
-- source:
--   https://github.com/liuchliuch/narrow-dnf-lean/blob/eecadd6a5ea0a331d6cf9fd5cb39fc6ec854b372/NarrowDNF/BourgainSquareFunction.lean#L112-L130

import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Real.Basic
import Mathlib.Logic.Equiv.Prod
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_NarrowDNF_Fourier

namespace NarrowDNF.BourgainSquareFunction
end NarrowDNF.BourgainSquareFunction
noncomputable section
open scoped BigOperators
open NarrowDNF
open NarrowDNF.BourgainSquareFunction
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem NarrowDNF.BourgainSquareFunction.low_degree_le_damped (a : (ι → Bool) → ℝ) (k m : ℕ) :
    (∑ s ∈ (Finset.univ.filter fun s => Fourier.degree s ≤ k), a s^2) ≤
      (3 : ℝ)^(m*k) * ∑ s, a s^2 / (3 : ℝ)^(m * Fourier.degree s) := by sorry
