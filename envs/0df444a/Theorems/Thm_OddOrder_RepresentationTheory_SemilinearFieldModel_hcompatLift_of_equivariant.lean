-- Prove2me | Theorems.Thm_OddOrder_RepresentationTheory_SemilinearFieldModel_hcompatLift_of_equivariant
-- name    : OddOrder.RepresentationTheory.SemilinearFieldModel.hcompatLift_of_equivariant
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-11-12T04:49:08.780029+00:00
-- url     : https://prove2.me/theorems/56f71d56-6e36-481b-9e61-cf65494d7860
-- title:
--   Lift compatibility from textbook $C$-equivariance of the field isomorphism
-- statement:
--   Let $r$ be a prime, $s$ a natural number, $G$ a group, $E,C\le G$ subgroups, $e:E\to\mathbb{F}_{r^s}$ an additive isomorphism, and $\mu:C\to\mathbb{F}_{r^s}^{\times}$ an injective homomorphism whose range is the group $U$ of norm-one units. Assume $C$ normalizes $E$ elementwise (for $v\in C$, $x\in E$, $vxv^{-1}\in E$) and that $e$ is $C$-equivariant:
--   $$e(vxv^{-1})=\mu(v)\cdot e(x)\qquad(v\in C,\ x\in E).$$
--   Then for every $u\in U$, the transported multiplication action of $u$ agrees with conjugation by the corresponding element of $C$ after transport along $e$:
--   $$\text{kernelTransport }e\circ(\text{mult. by }u)=\mathrm{conj}\bigl(\text{complementTransport }\mu\ u\bigr)\circ\text{kernelTransport }e$$
--   as monoid homomorphisms (the `hcompatLift` condition demanded by `fieldModelEmbedding`).
--
--   This derives the `SemidirectProduct.lift` compatibility from the textbook equivariance of Peterfalvi (14.2)(a); it is the generic bridge used on both the $P/U$ and $Q/V$ sides.
--
--   **Formalization Note** `kernelTransport`, `complementTransport`, `normOneMulAction` are project definitions; the proof transports the conjugation identity across $e$ and inverts $\mu$ inside `complementTransport`.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/GroupTheory/RepresentationTheory/SemilinearFieldModel.lean#L157-L206

import Definitions.Def_OddOrder_BG_AppC_NormSet
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_SemilinearFieldModel

namespace OddOrder.RepresentationTheory.SemilinearFieldModel

open OddOrder.BG.AppC.NormSet

variable {G : Type*} [Group G]

set_option backward.isDefEq.respectTransparency false in

theorem hcompatLift_of_equivariant {r s : ℕ} [Fact r.Prime] {E C : Subgroup G}
    (e : Additive ↥E ≃+ GaloisField r s)
    (μ : ↥C →* (GaloisField r s)ˣ) (hμ_inj : Function.Injective μ)
    (hμ_range : μ.range = normOneUnits r s)
    (hCE : ∀ (v : ↥C) (x : ↥E), (v : G) * (x : G) * (v : G)⁻¹ ∈ E)
    (hcompat : ∀ (v : ↥C) (x : ↥E),
      e (Additive.ofMul (⟨(v : G) * (x : G) * (v : G)⁻¹, hCE v x⟩ : ↥E))
        = ((μ v : (GaloisField r s)ˣ) : GaloisField r s) * e (Additive.ofMul x)) :
    ∀ u : ↥(normOneUnits r s),
      (kernelTransport e).comp ((normOneMulAction r s u).toMonoidHom)
        = (MulAut.conj (complementTransport μ hμ_inj hμ_range u)).toMonoidHom.comp
            (kernelTransport e) := by sorry

end OddOrder.RepresentationTheory.SemilinearFieldModel
