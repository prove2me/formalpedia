-- Prove2me | Theorems.Thm_OddOrder_RepresentationTheory_SemilinearFieldModel_fieldModelEmbedding
-- name    : OddOrder.RepresentationTheory.SemilinearFieldModel.fieldModelEmbedding
-- status  : Proved
-- author  : @burkh4rt
-- created : 2026-11-12T04:49:00.309455+00:00
-- url     : https://prove2.me/theorems/39b8816f-aa24-4651-b0ee-43509440d539
-- title:
--   Embedding of the norm-one Frobenius group from a field-model identification
-- statement:
--   Let $r$ be a prime, $s$ a natural number, $G$ a group, and $E,C\le G$ subgroups. Suppose given
--
--   * an additive isomorphism $e:E\to\mathbb{F}_{r^s}$;
--   * an injective homomorphism $\mu:C\to\mathbb{F}_{r^s}^{\times}$ whose range is the group $U$ of norm-one units of $\mathbb{F}_{r^s}$;
--   * the compatibility condition `hcompatLift`: for every $u\in U$, the transport of the multiplication action of $u$ on the additive group (via $e$) equals conjugation by the element of $C$ corresponding to $u$ under $\mu$, composed with the transport of the kernel (stated with `kernelTransport e` and `complementTransport μ`);
--   * $E\cap C=1$.
--
--   Then there is an injective homomorphism $\sigma:\mathbb{F}_{r^s}\rtimes U\to G$ from the norm-one Frobenius group `normOneFrobeniusGroup r s` such that $\sigma$ maps the additive kernel $\mathbb{F}_{r^s}$ onto $E$ and the complement $U$ onto $C$.
--
--   **Formalization Note** The compatibility hypothesis is the equation of monoid homomorphisms required by `SemidirectProduct.lift`; `kernelTransport`, `complementTransport` and `normOneMulAction` are project-specific encodings.
-- source:
--   Yawara Ishida, Lean 4 formalization of the Feit–Thompson (odd order) theorem, github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0), https://github.com/yawara/odd-order/blob/20a6fccbb63c0b138acda9f7fafd798c42f9441b/OddOrder/GroupTheory/RepresentationTheory/SemilinearFieldModel.lean#L208-L283

import Definitions.Def_OddOrder_BG_AppC_NormSet
import Definitions.Def_OddOrder_GroupTheory_RepresentationTheory_SemilinearFieldModel

namespace OddOrder.RepresentationTheory.SemilinearFieldModel

open OddOrder.BG.AppC.NormSet

variable {G : Type*} [Group G]

theorem fieldModelEmbedding {r s : ℕ} [Fact r.Prime] {E C : Subgroup G}
    (e : Additive ↥E ≃+ GaloisField r s)
    (μ : ↥C →* (GaloisField r s)ˣ) (hμ_inj : Function.Injective μ)
    (hμ_range : μ.range = normOneUnits r s)
    (hcompatLift : ∀ u : ↥(normOneUnits r s),
      (kernelTransport e).comp ((normOneMulAction r s u).toMonoidHom)
        = (MulAut.conj (complementTransport μ hμ_inj hμ_range u)).toMonoidHom.comp
            (kernelTransport e))
    (hEC_disj : E ⊓ C = ⊥) :
    ∃ σ : normOneFrobeniusGroup r s →* G,
      Function.Injective σ ∧
      (SemidirectProduct.inl :
          additiveFieldGroup r s →* normOneFrobeniusGroup r s).range.map σ = E ∧
      (SemidirectProduct.inr :
          ↥(normOneUnits r s) →* normOneFrobeniusGroup r s).range.map σ = C := by sorry

end OddOrder.RepresentationTheory.SemilinearFieldModel
