-- Prove2me | Theorems.Thm_OAI_BalancedTransport_Effectivity_computable_sum_range
-- name    : OAI.BalancedTransport.Effectivity.computable_sum_range
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T04:06:42.350025+00:00
-- url     : https://prove2.me/theorems/0978d524-110e-4c61-89bc-1b6013d8327b
-- title:
--   Finite sums of a computable rational sequence are computable
-- statement:
--   Let $\alpha$ be an encodable type and $f:\alpha\times\mathbb N\to\mathbb Q$ computable. Then
--   $$
--   (a,n)\mapsto\sum_{i<n}f(a,i)
--   $$
--   is computable.
--
--   This covers the partial sums used to approximate exponentials and to evaluate the polynomials in the derivatives of $e^{-1/x}$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MathematicalPhysics/NavierStokes/BalancedTransport/RationalAlgorithms.lean#L113-L126

import Mathlib
import Definitions.Def_BalancedThreeStack
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_FlatBounds
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_EffectiveArithmetic
import Definitions.Def_OAI_MathematicalPhysics_NavierStokes_BalancedTransport_RationalAlgorithms

open OAI OAI.BalancedTransport OAI.BalancedTransport.Effectivity

theorem OAI.BalancedTransport.Effectivity.computable_sum_range {α : Type*} [Primcodable α]
    {f : α → ℕ → ℚ} (hf : Computable₂ f) :
    Computable₂ (fun a n => ∑ i ∈ Finset.range n, f a i) := by sorry
