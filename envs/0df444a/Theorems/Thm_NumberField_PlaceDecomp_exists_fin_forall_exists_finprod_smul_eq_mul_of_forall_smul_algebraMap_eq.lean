-- Prove2me | Theorems.Thm_NumberField_PlaceDecomp_exists_fin_forall_exists_finprod_smul_eq_mul_of_forall_smul_algebraMap_eq
-- name    : NumberField.PlaceDecomp.exists_fin_forall_exists_finprod_smul_eq_mul_of_forall_smul_algebraMap_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.351487+00:00
-- url     : https://prove2.me/theorems/19cdf4c3-30cb-5e32-9598-84efe0ffb7bd
-- title:
--   Norm-coset representatives descend below the decomposition field
-- statement:
--   Let $E$, $L$, $F$ be number fields with $E \subseteq L \subseteq F$ (algebra structures forming a scalar tower), with $F/E$ and $F/L$ Galois, and let $w$ be a height-one prime of $\mathcal{O}_F$. Write $w_L$ for the prime of $\mathcal{O}_L$ lying under $w$, and assume the compatibility $h$ that the prime of $\mathcal{O}_E$ under $w$ coincides with the prime $v$ of $\mathcal{O}_E$ under $w_L$. For a Galois layer, `decomp` denotes the decomposition subgroup: the subgroup of automorphisms preserving the valuation subring of the $w$-adic valuation of $F$. Assume that every $\sigma$ in the decomposition subgroup of $w$ in $\mathrm{Gal}(F/E)$ fixes $\mathrm{algebraMap}\,L\,F\,(x)$ for all $x \in L$. Assume further that for some $m \in \mathbb{N}$ there are units $d_0,\dots,d_{m-1}$ of the completion $L_{w_L}$ such that every unit $a'$ of $L_{w_L}$ admits an index $j$ and a unit $b$ of $F_w$ with $\prod^{\mathrm{f}}_{\tau \in \mathrm{decomp}(F/L,w)} \tau \cdot b$ equal, in $F_w$, to the image of $a'd_j^{-1}$ under the semialgebra map $L_{w_L} \to F_w$ attached to $w$ over $w_L$. The conclusion asserts the existence of units $c_0,\dots,c_{m-1}$ of $E_v$ such that every unit $a$ of $E_v$ admits an index $k$ and a unit $b$ of $F_w$ with $\prod^{\mathrm{f}}_{\sigma \in \mathrm{decomp}(F/E,w)} \sigma \cdot b$ equal, in $F_w$, to the image of $ac_k^{-1}$ under the semialgebra map $E_v \to F_w$ attached to the extension $\langle w, h\rangle$.
--
--   The statement transfers a bound on the index of the subgroup of local "norms" (conjugate products over the decomposition group) from an intermediate field $L$ pointwise fixed by the decomposition group of $w$ down to the base field $E$, the point being that $E_v$ and $L_{w_L}$ then have the same image inside $F_w$. It serves as the base step in the induction bounding the local norm index for layers with commutative decomposition group, and is cited by [`NumberField.PlaceDecomp.exists_fin_forall_exists_finprod_smul_eq_mul_of_isMulCommutative_decomp`](thm.html#NumberField.PlaceDecomp.exists_fin_forall_exists_finprod_smul_eq_mul_of_isMulCommutative_decomp).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_PlaceDecomp_exists_fin_forall_exists_finprod_smul_eq_mul_of_forall_smul_algebraMap_eq.lean

import Mathlib
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_DedekindDomain_Completion_BaseChange

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxSynthPendingDepth 3
open IsDedekindDomain NumberField
open scoped NumberField.PlaceDecomp

theorem NumberField.PlaceDecomp.exists_fin_forall_exists_finprod_smul_eq_mul_of_forall_smul_algebraMap_eq
    (E L F : Type) [Field E] [NumberField E] [Field L] [NumberField L] [Field F] [NumberField F]
    [Algebra E L] [Algebra L F] [Algebra E F] [IsScalarTower E L F] [IsGalois E F] [IsGalois L F]
    (w : HeightOneSpectrum (𝓞 F))
    (h : HeightOneSpectrum.under (𝓞 E) w =
      HeightOneSpectrum.under (𝓞 E) (HeightOneSpectrum.under (𝓞 L) w))
    (hfix : ∀ (σ : ↥(NumberField.PlaceDecomp.decomp E F w)) (x : L),
      (σ : F ≃ₐ[E] F) (algebraMap L F x) = algebraMap L F x)
    (m : ℕ) (d : Fin m → ((HeightOneSpectrum.under (𝓞 L) w).adicCompletion L)ˣ)
    (hd : ∀ a' : ((HeightOneSpectrum.under (𝓞 L) w).adicCompletion L)ˣ,
      ∃ (j : Fin m) (b : (w.adicCompletion F)ˣ),
        (((∏ᶠ τ : ↥(NumberField.PlaceDecomp.decomp L F w), τ • b : (w.adicCompletion F)ˣ) : (w.adicCompletion F)ˣ) :
            w.adicCompletion F) =
          HeightOneSpectrum.Extension.adicCompletionSemialgHom L F
            (⟨w, rfl⟩ : (HeightOneSpectrum.under (𝓞 L) w).Extension (𝓞 F))
            ((a' * (d j)⁻¹ : ((HeightOneSpectrum.under (𝓞 L) w).adicCompletion L)ˣ) :
              (HeightOneSpectrum.under (𝓞 L) w).adicCompletion L)) :
    ∃ c : Fin m → ((HeightOneSpectrum.under (𝓞 E) (HeightOneSpectrum.under (𝓞 L) w)).adicCompletion E)ˣ,
      ∀ a : ((HeightOneSpectrum.under (𝓞 E) (HeightOneSpectrum.under (𝓞 L) w)).adicCompletion E)ˣ,
        ∃ (k : Fin m) (b : (w.adicCompletion F)ˣ),
          (((∏ᶠ σ : ↥(NumberField.PlaceDecomp.decomp E F w), σ • b : (w.adicCompletion F)ˣ) : (w.adicCompletion F)ˣ) :
              w.adicCompletion F) =
            HeightOneSpectrum.Extension.adicCompletionSemialgHom E F
              (⟨w, h⟩ : (HeightOneSpectrum.under (𝓞 E) (HeightOneSpectrum.under (𝓞 L) w)).Extension (𝓞 F))
              ((a * (c k)⁻¹ : ((HeightOneSpectrum.under (𝓞 E) (HeightOneSpectrum.under (𝓞 L) w)).adicCompletion E)ˣ) :
                (HeightOneSpectrum.under (𝓞 E) (HeightOneSpectrum.under (𝓞 L) w)).adicCompletion E) := by sorry
