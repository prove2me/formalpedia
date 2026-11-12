-- Prove2me | Theorems.Thm_OddOrder_BG_AppC_FieldNormalizerData_normN_two_mul_sub_one_of_sigma_first_k_three_decomposition
-- name    : OddOrder.BG.AppC.FieldNormalizerData.normN_two_mul_sub_one_of_sigma_first_k_three_decomposition
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-11-12T05:21:57.834682+00:00
-- url     : https://prove2.me/theorems/ceb71cd8-4025-4fbc-a4d4-16256e6a5d1f
-- title:
--   BG Lemma C.3, Step 4: a normal-form relation forces $N(2w-1)=1$
-- statement:
--   Let $p,q$ be natural numbers with $p$ prime, $G$ a group, and `data : FieldNormalizerData p q G` the field-normalizer data of Bender--Glauberman Appendix C (a monomorphism $\sigma:H=P\rtimes U\to G$ of the norm-one Frobenius group $H$ together with the abelian $p'$-subgroup $Q$ and element $y\in Q$ of Hypothesis (B), and Condition (A)). Write $s=\sigma(1_{P_0})$ for the image of the distinguished generator of the prime-field line $P_0$. Let $w,u_1,v_1$ be norm-one units of $\mathbb{F}_{p^q}$, and suppose
--   $$ s\,\sigma(w)\,s^{-2}=\sigma(u_1)\,\sigma(c_{-1})\,\sigma(v_1) $$
--   in $G$, where $\sigma(u)$ denotes the image of the complement element $u\in U$ and $c_{-1}$ is the element $-1$ of the prime-field line $P_0$. Then, with $N$ the field norm of $\mathbb{F}_{p^q}$ over $\mathbb{F}_p$,
--   $$N(2w-1)=1.$$
--
--   This is the finite-field reading of the final paragraph of Step 4 of Lemma C.3: once the first factor of the $k=3$ normal form has middle prime-line factor $s^{-1}$, the additive coordinate yields a norm-one condition on the complement element $w$.
--
--   **Formalization Note** Here $N$ is `NormSet.normN p q`, the product $\prod_{i<q}x^{p^i}$ in `GaloisField p q`; `primeLineElement p q c` is the image of $c\in\mathbb{Z}/p$ in the additive kernel.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/BG/AppC_LemmaC3_ConjugateLine.lean#L610-L676

import Definitions.Def_OddOrder_BG_AppC_LemmaC3_Setup
import Definitions.Def_OddOrder_Mathlib_Subgroup
import Definitions.Def_OddOrder_Isaacs_Ch04_Commutators_Main_ThreeSubgroupsCoprime
import Definitions.Def_OddOrder_BG_AppC_LemmaC3_ConjugateLine

namespace OddOrder.BG.AppC

open scoped Pointwise

open scoped BigOperators

variable {p q : ℕ} [Fact p.Prime] {G : Type*} [Group G]

namespace FieldNormalizerData

theorem normN_two_mul_sub_one_of_sigma_first_k_three_decomposition
    (data : FieldNormalizerData p q G)
    (w u₁ v₁ : NormSet.normOneUnits p q)
    (hdec : data.s *
          data.sigma (SemidirectProduct.inr w : NormSet.normOneFrobeniusGroup p q) *
        data.s ^ (-2 : ℤ) =
      data.sigma (SemidirectProduct.inr u₁ : NormSet.normOneFrobeniusGroup p q) *
        data.sigma (primeLineElement p q (-1 : ZMod p)) *
          data.sigma (SemidirectProduct.inr v₁ : NormSet.normOneFrobeniusGroup p q)) :
    NormSet.normN p q
      ((2 : GaloisField p q) *
          (((w : NormSet.normOneUnits p q) :
              (GaloisField p q)ˣ) :
              GaloisField p q) - 1) = 1 := by sorry

end FieldNormalizerData

end OddOrder.BG.AppC
