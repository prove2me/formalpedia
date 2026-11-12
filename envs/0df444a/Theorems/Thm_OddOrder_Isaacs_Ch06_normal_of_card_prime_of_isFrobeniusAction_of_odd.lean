-- Prove2me | Theorems.Thm_OddOrder_Isaacs_Ch06_normal_of_card_prime_of_isFrobeniusAction_of_odd
-- name    : OddOrder.Isaacs.Ch06.normal_of_card_prime_of_isFrobeniusAction_of_odd
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-11-12T05:46:42.672199+00:00
-- url     : https://prove2.me/theorems/450f5231-6363-4869-b565-4930adfc3077
-- title:
--   Huppert V.8.18(b): in a Frobenius complement of odd order every subgroup of prime order is normal
-- statement:
--   Let $A$ be a finite group acting on a finite nontrivial group $U$ (`MulDistribMulAction A U`) with a Frobenius action (`IsFrobeniusAction A U`: every nonidentity element of $A$ fixes only the identity of $U$), such that $|A|$ is odd. Let $R\le A$ be a subgroup of prime order $r$. Then $R$ is normal in $A$.
--
--   This is Huppert, *Endliche Gruppen I*, Chapter V, Satz 8.18 b). The complement $A$ is a Z-group, so $N=A'$ is cyclic and normal, with $A/N$ cyclic and $\gcd(|N|,[A:N])=1$. If $r\mid|N|$, the unique subgroup of order $r$ in the cyclic group $N$ is characteristic and every order-$r$ subgroup of $A$ lies in $N$. If $r\nmid|N|$, then $R$ centralizes $N$ (previous step) and a commutator argument shows every conjugate of $R$ equals $R$.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Isaacs/Ch06_FrobeniusActions/OddComplement.lean#L298-L399

import Definitions.Def_OddOrder_Isaacs_Ch06_FrobeniusActions_Main
import Definitions.Def_OddOrder_Isaacs_Ch04_Commutators_Main_CommutatorBasics
import Definitions.Def_OddOrder_Isaacs_Ch04_Commutators_Main_ThreeSubgroupsCoprime
import Definitions.Def_OddOrder_Isaacs_Ch04_Commutators_Main_BaerTrick
import Definitions.Def_OddOrder_Isaacs_Ch04_Commutators_Main_ChainNilpotent
import Definitions.Def_OddOrder_Isaacs_Ch04_Commutators_ForwardFromCh03
import Definitions.Def_OddOrder_Isaacs_Ch04_Commutators_Main_ThreeSubgroups
import Definitions.Def_OddOrder_GroupTheory_ElementaryAbelian
import Definitions.Def_OddOrder_Isaacs_Ch06_FrobeniusActions_OddComplement
import Mathlib.GroupTheory.SpecificGroups.ZGroup

namespace OddOrder.Isaacs.Ch06

open scoped IsMulCommutative

open scoped commutatorElement

open OddOrder.Isaacs.Ch04

variable {A U : Type*} [Group A] [Finite A] [Group U] [Finite U] [Nontrivial U]
  [MulDistribMulAction A U]

theorem normal_of_card_prime_of_isFrobeniusAction_of_odd
    (hFrob : IsFrobeniusAction A U) (hodd : Odd (Nat.card A))
    {R : Subgroup A} {r : ℕ} (hr : r.Prime) (hRcard : Nat.card ↥R = r) :
    R.Normal := by sorry

end OddOrder.Isaacs.Ch06
