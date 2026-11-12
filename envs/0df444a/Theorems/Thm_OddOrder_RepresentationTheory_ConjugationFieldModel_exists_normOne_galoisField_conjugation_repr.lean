-- Prove2me | Theorems.Thm_OddOrder_RepresentationTheory_ConjugationFieldModel_exists_normOne_galoisField_conjugation_repr
-- name    : OddOrder.RepresentationTheory.ConjugationFieldModel.exists_normOne_galoisField_conjugation_repr
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-11-12T05:31:16.590009+00:00
-- url     : https://prove2.me/theorems/4a9f6844-774b-4496-b206-444789e76b96
-- title:
--   Faithful elementary abelian conjugation action gives the norm-one Galois-field model
-- statement:
--   Let $G$ be a finite group, $r,s$ primes with $s$ odd, and $E,C\le G$ subgroups such that:
--
--   * $E$ is elementary abelian of exponent $r$ and $|E|=r^s$;
--   * $C$ is commutative and normalizes $E$, with $|C|=\dfrac{r^s-1}{r-1}$;
--   * $C\cap C_G(E)=1$ (the action of $C$ on $E$ is faithful).
--
--   Then there exist an additive isomorphism $e:E\to\mathbb{F}_{r^s}$ and an injective homomorphism $\mu:C\to\mathbb{F}_{r^s}^{\times}$ such that the range of $\mu$ is the group of norm-one units $U=\{u:N(u)=1\}$ of $\mathbb{F}_{r^s}$, and for all $c\in C$ and $x\in E$,
--   $$e(cxc^{-1})=\mu(c)\cdot e(x).$$
--
--   That is, conjugation by $C$ on $E$ is realized as multiplication by norm-one units on the field $\mathbb{F}_{r^s}$. No field structure or representation is assumed in advance; the field is constructed by a Singer-type argument.
--
--   **Formalization Note** $e$ is an equivalence `Additive ↥E ≃+ GaloisField r s`, the group of norm-one units is `normOneUnits r s`, and the conjugation action is encoded by `conjugate hCnorm c x`.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/GroupTheory/RepresentationTheory/ConjugationFieldModel.lean#L95-L197

import Definitions.Def_OddOrder_BG_AppC_NormSet
import Definitions.Def_OddOrder_BG_Ch1_Preliminary_OperatorMaschke
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_SingerField
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_ConjugationFieldModel

namespace OddOrder.RepresentationTheory.ConjugationFieldModel

open OddOrder.GroupTheory

open OddOrder.BG.AppC.NormSet

variable {G : Type*} [Group G]

set_option maxHeartbeats 1000000 in
-- The Singer construction expands a large group-algebra module term during elaboration; this
-- local limit matches the existing concrete `P/U` instantiation.
open scoped IsMulCommutative in

theorem exists_normOne_galoisField_conjugation_repr [Finite G]
    {r s : ℕ} (hr : r.Prime) (hs : s.Prime) (hsodd : Odd s)
    {E C : Subgroup G} (hE : IsElementaryAbelian r ↥E)
    (hCcomm : IsMulCommutative ↥C)
    (hCnorm : C ≤ Subgroup.normalizer (E : Set G))
    (hcardE : Nat.card ↥E = r ^ s)
    (hcardC : Nat.card ↥C = (r ^ s - 1) / (r - 1))
    (hfaith : C ⊓ Subgroup.centralizer (E : Set G) = ⊥) :
    letI : Fact r.Prime := ⟨hr⟩
    ∃ (e : Additive ↥E ≃+ GaloisField r s) (μ : ↥C →* (GaloisField r s)ˣ),
      Function.Injective μ ∧
      μ.range = normOneUnits r s ∧
      ∀ (c : ↥C) (x : ↥E),
        e (Additive.ofMul (conjugate hCnorm c x)) =
          ((μ c : (GaloisField r s)ˣ) : GaloisField r s) * e (Additive.ofMul x) := by sorry

end OddOrder.RepresentationTheory.ConjugationFieldModel
