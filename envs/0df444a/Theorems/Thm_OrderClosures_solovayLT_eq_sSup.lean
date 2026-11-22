-- Prove2me | Theorems.Thm_OrderClosures_solovayLT_eq_sSup
-- name    : OrderClosures.solovayLT_eq_sSup
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:56:42.987816+00:00
-- url     : https://prove2.me/theorems/d65ba138-fe3e-4538-b29b-537cd543a228
-- title:
--   Order Closures: solovay LT eq s Sup
-- statement:
--   Expresses the strict-order event as a supremum of basic generators; used
--   to place it in every complete subalgebra containing `solovayA`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/Solovay.lean#L310-L321
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/OrderClosures/Solovay.lean#L310-L321

module
public import Definitions.Def_LeanPool_OrderClosures_OrderAdherence
public import Mathlib.Order.Heyting.Regular
public import Mathlib.Order.BooleanSubalgebra
public import Mathlib.SetTheory.Cardinal.Order
public import Mathlib.Topology.Category.Stonean.Basic
public import Mathlib.Order.PrimeSeparator
public import Mathlib.Topology.ContinuousMap.StoneWeierstrass
public import Definitions.Def_LeanPool_OrderClosures_Solovay
set_option autoImplicit true
@[expose] public section
public section
open Set
noncomputable section
open OrderClosures
universe u
variable (Gamma : Type u) [LinearOrder Gamma] [TopologicalSpace Gamma]
  [DiscreteTopology Gamma]

theorem OrderClosures.solovayLT_eq_sSup (n : ℕ) (eta : Gamma) :
    solovayLT Gamma n eta =
      sSup (solovayA Gamma n '' Set.Iio eta) := by sorry
