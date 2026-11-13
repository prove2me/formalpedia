-- Prove2me | Theorems.Thm_OddOrder_Peterfalvi_S16_frobenius_PU_of_field_repr
-- name    : OddOrder.Peterfalvi.S16.frobenius_PU_of_field_repr
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-11-12T17:32:55.47853+00:00
-- url     : https://prove2.me/theorems/ed97aca5-969f-473b-8009-5e32091f122e
-- title:
--   Peterfalvi (14.2)/(14.7): $S'=P\rtimes U$ is a Frobenius group with kernel $P$ from a field model
-- statement:
--   Let $G$ be a finite minimal simple odd-order group and `hyp` a Peterfalvi §14 configuration with primes $p,q$ and subgroups $S,P,U$ of `hyp.base`. Let $\mathbb{F}=\mathrm{GF}(p^q)$ and assume there exist an additive isomorphism $e : P\cong\mathbb{F}$ and an **injective** homomorphism $\mu : U\to\mathbb{F}^\times$ with $e(vxv^{-1})=\mu(v)\,e(x)$ for all $v\in U$, $x\in P$. Then the derived subgroup $S'$ of $S$ (as a group, `↥(derivedInG hyp.base.S)`) is a Frobenius group with kernel $P$ and complement $U$, i.e.
--   $$\texttt{IsFrobeniusGroup}\ S'\ (P\cap S')\ (U\cap S'),$$
--   where the subgroups are taken via `subgroupOf (derivedInG S)`.
--
--   A nonidentity element of $U$ fixing a nonidentity point of $P$ would force $\mu(u)=1$, hence $u=1$ by injectivity; this is the Frobenius (semiregularity) condition. The value $|U|=(p^q-1)/(p-1)$ is not needed.
--
--   **Formalization Note.** `IsFrobeniusGroup` is from `OddOrder.Isaacs.Ch06`; the structural facts $S'=PU$, $P\cap U=1$, $P\ne 1$, $U\ne1$ are supplied by the §13 configuration and are not hypotheses of the theorem.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/Peterfalvi/S16_NonExistenceG/SubgroupM.lean#L20-L152

import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_ConjugationFieldModel
import Definitions.Def_OddOrder_Peterfalvi_S16_NonExistenceG_SubgroupMCore
import Definitions.Def_OddOrder_Peterfalvi_S16_NonExistenceG_SubgroupM

namespace OddOrder.Peterfalvi.S16

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

open scoped BigOperators

variable {G : Type*} [Group G]

open scoped OddOrder.Peterfalvi.S12.FiniteInduce in

theorem frobenius_PU_of_field_repr [Finite G] (hG : OddOrder.BG.IsMinimalSimpleOdd G)
    (hyp : Hypothesis (G := G))
    (hrepr : letI : Fact hyp.base.p.Prime := ⟨hyp.base.p_prime⟩
      ∃ (e : Additive ↥hyp.base.P ≃+ GaloisField hyp.base.p hyp.base.q)
        (μ : ↥hyp.base.U →* (GaloisField hyp.base.p hyp.base.q)ˣ),
        Function.Injective μ ∧
        ∀ (v : ↥hyp.base.U) (x : ↥hyp.base.P),
          e (Additive.ofMul (⟨(v : G) * (x : G) * (v : G)⁻¹, conj_mem_P hyp v x⟩ :
              ↥hyp.base.P))
            = ((μ v : (GaloisField hyp.base.p hyp.base.q)ˣ) :
                GaloisField hyp.base.p hyp.base.q) * e (Additive.ofMul x)) :
    OddOrder.Isaacs.Ch06.IsFrobeniusGroup ↥(derivedInG hyp.base.S)
      (hyp.base.P.subgroupOf (derivedInG hyp.base.S))
      (hyp.base.U.subgroupOf (derivedInG hyp.base.S)) := by sorry

end OddOrder.Peterfalvi.S16
