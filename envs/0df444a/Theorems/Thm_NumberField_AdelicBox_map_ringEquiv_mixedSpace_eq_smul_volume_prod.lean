-- Prove2me | Theorems.Thm_NumberField_AdelicBox_map_ringEquiv_mixedSpace_eq_smul_volume_prod
-- name    : NumberField.AdelicBox.map_ringEquiv_mixedSpace_eq_smul_volume_prod
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.529639+00:00
-- url     : https://prove2.me/theorems/0e952910-6618-5547-a4ce-c5aee4a19621
-- title:
--   Haar measure on A_F as a scaled product measure
-- statement:
--   Let $F$ be a number field, let the adele ring $\mathbb{A}_F=\mathbb{A}_{F,\infty}\times\mathbb{A}_{F,f}$ and the finite adele ring $\mathbb{A}_{F,f}$ carry measurable structures that are the Borel structures of their topologies, and let $\mu$ be an additive Haar measure on $\mathbb{A}_F$ and $\nu$ an additive Haar measure on $\mathbb{A}_{F,f}$. Write $e$ for the canonical ring isomorphism `InfiniteAdeleRing.ringEquiv_mixedSpace` from $\mathbb{A}_{F,\infty}$ to the mixed space $F_\mathbb{R}=\mathbb{R}^{r_1}\times\mathbb{C}^{r_2}$, let $\hat{\mathcal{O}}=$ `integralFiniteAdeles` be the set of finite adeles whose component at every height one prime $v$ of $\mathcal{O}_F$ lies in the valuation ring of $F_v$, and let the adelic box be the set of adeles $x$ with $e(x_\infty)$ in the fundamental domain of the $\mathbb{Z}$-span of `mixedEmbedding.latticeBasis` and $x_f\in\hat{\mathcal{O}}$. Set $$c=\frac{\mu(\text{adelic box})}{\operatorname{covol}(\text{integerLattice }F)\cdot\nu(\hat{\mathcal{O}})},$$ the covolume being taken with respect to Lebesgue measure on $F_\mathbb{R}$, and all three quantities read as real numbers. The assertion is twofold: $c>0$, and the push-forward of $\mu$ along $x\mapsto(e(x_\infty),x_f)$ equals $c$ times the product of Lebesgue measure on $F_\mathbb{R}$ with $\nu$.
--
--   This is the normalisation of an arbitrary additive Haar measure on $\mathbb{A}_F$ as an explicit positive multiple of the tensor product of Lebesgue measure on the mixed space with a Haar measure on the finite adeles, the constant being computed on the adelic box; it rests on the uniqueness of Haar measure on $\mathbb{A}_F$ ([`NumberField.AdelicFourier.exists_smul_eq_of_isAddHaarMeasure_adeleRing`](thm.html#NumberField.AdelicFourier.exists_smul_eq_of_isAddHaarMeasure_adeleRing)) together with second countability of the adele ring. It is the measure-theoretic input for Fubini-type factorisations of adelic integrals of pure tensors and for the evaluation of the measure of the adelic box in terms of the discriminant, both used in the adelic Fourier analysis on $\mathbb{A}_F$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_AdelicBox_map_ringEquiv_mixedSpace_eq_smul_volume_prod.lean

import Definitions.Def_NumberField_AdelicBox
import Mathlib.Algebra.Module.ZLattice.Covolume

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicBox IsDedekindDomain

open scoped Classical in

theorem NumberField.AdelicBox.map_ringEquiv_mixedSpace_eq_smul_volume_prod
    (F : Type) [Field F] [NumberField F]
    [MeasurableSpace (AdeleRing (𝓞 F) F)] [BorelSpace (AdeleRing (𝓞 F) F)]
    (μ : Measure (AdeleRing (𝓞 F) F)) [μ.IsAddHaarMeasure]
    [MeasurableSpace (FiniteAdeleRing (𝓞 F) F)] [BorelSpace (FiniteAdeleRing (𝓞 F) F)]
    (ν : Measure (FiniteAdeleRing (𝓞 F) F)) [ν.IsAddHaarMeasure] :
    0 < (μ (adelicBox F)).toReal /
        (ZLattice.covolume (mixedEmbedding.integerLattice F) volume
          * (ν (integralFiniteAdeles (𝓞 F) F)).toReal) ∧
    Measure.map (fun x : AdeleRing (𝓞 F) F => (InfiniteAdeleRing.ringEquiv_mixedSpace F x.1, x.2)) μ
      = ((μ (adelicBox F)).toReal /
          (ZLattice.covolume (mixedEmbedding.integerLattice F) volume
            * (ν (integralFiniteAdeles (𝓞 F) F)).toReal)).toNNReal
        • (volume : Measure (mixedEmbedding.mixedSpace F)).prod ν := by sorry
