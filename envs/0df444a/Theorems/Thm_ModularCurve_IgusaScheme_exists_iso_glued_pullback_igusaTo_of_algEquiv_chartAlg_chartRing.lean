-- Prove2me | Theorems.Thm_ModularCurve_IgusaScheme_exists_iso_glued_pullback_igusaTo_of_algEquiv_chartAlg_chartRing
-- name    : ModularCurve.IgusaScheme.exists_iso_glued_pullback_igusaTo_of_algEquiv_chartAlg_chartRing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:39.721416+00:00
-- url     : https://prove2.me/theorems/0c2d7488-b7e8-5a93-91ef-89d0aa785689
-- title:
--   The K-fibre of the Igusa scheme as a glued two-chart curve
-- statement:
--   Fix $N\ge 1$ and a prime $\ell$, and write $\mathbb{Z}_{(\ell)}$ for the subring [`GaloisRep.ratLocalizedAt ℓ`](def/GaloisRep_Flat.html#L8) of $\mathbb{Q}$ consisting of the rationals whose denominator is coprime to $\ell$. Let $K$ be a field that is a $\mathbb{Z}_{(\ell)}$-algebra, $L$ a field extension of $K$, and $t \in L$ with $t \neq 0$. Inside the full modular function field $F =$ `modularFunctionFieldFull N` (the subfield of $\mathbb{Q}((q))$ generated over $\mathbb{Q}$ by the divisor expansions of level $N$) let $\mathcal{O}_{\mathrm{fin}} =$ `chartAlgFin N ℓ` and $\mathcal{O}_{\infty} =$ `chartAlgInf N ℓ` be the two $\mathbb{Z}_{(\ell)}$-chart algebras `chartAlg N ℓ` attached to $\{j\}$ and $\{j^{-1}\}$, where $j =$ `jFull N`; on the other side let `CurveModel.chartRing K {t}` and `CurveModel.chartRing K {t⁻¹}` be the integral closures in $L$ of $K[t]$ and of $K[t^{-1}]$. Assume given $K$-algebra isomorphisms $e_{\mathrm{fin}} \colon K \otimes_{\mathbb{Z}_{(\ell)}} \mathcal{O}_{\mathrm{fin}} \to \overline{K[t]}^{L}$ and $e_{\infty} \colon K \otimes_{\mathbb{Z}_{(\ell)}} \mathcal{O}_{\infty} \to \overline{K[t^{-1}]}^{L}$ with $e_{\mathrm{fin}}(1 \otimes j) = t$ and $e_{\infty}(1 \otimes j^{-1}) = t^{-1}$, and compatible in the sense that for all $b \in \mathcal{O}_{\mathrm{fin}}$, $b' \in \mathcal{O}_{\infty}$ and $n \in \mathbb{N}$, the relation $b = b' \cdot j^{n}$ in $F$ implies $e_{\mathrm{fin}}(1 \otimes b) = e_{\infty}(1 \otimes b') \cdot t^{n}$ in $L$. The conclusion asserts the existence of a morphism $e_s$ from `CurveModel.glued K t`, the pushout of the two affine charts $\operatorname{Spec} \overline{K[t]}^{L}$ and $\operatorname{Spec} \overline{K[t^{-1}]}^{L}$ along their overlap, to the fibre product of `igusaTo N ℓ` (the structure morphism of [`ModularCurve.IgusaScheme N ℓ`](def/ModularCurve_IgusaScheme.html#L255), itself the pushout of the two $\mathbb{Z}_{(\ell)}$-charts, over $\operatorname{Spec} \mathbb{Z}_{(\ell)}$) with $\operatorname{Spec}$ of $\mathbb{Z}_{(\ell)} \to K$, together with the assertion that $e_s$ is an isomorphism, such that: $e_s$ followed by the second projection is `CurveModel.gluedToBase K t`; and, composing with the first projection, the restriction of $e_s$ along the finite chart $\iota_0$ equals $\operatorname{Spec}$ of the ring map $b \mapsto e_{\mathrm{fin}}(1 \otimes b)$ followed by `ιFin N ℓ`, while its restriction along the chart at infinity $\iota_\infty$ equals $\operatorname{Spec}$ of $b' \mapsto e_{\infty}(1 \otimes b')$ followed by `ιInf N ℓ`.
--
--   This identifies the base change to $K$ of the two-chart $\mathbb{Z}_{(\ell)}$-model of the modular curve with the glued curve built from a generator $t$ of the function field, compatibly with the chart structures on both sides; it is the version for an arbitrary field $K$ over $\mathbb{Z}_{(\ell)}$ of the corresponding generic-fibre identification. It is used in the construction of curve models for fibres of the Igusa scheme and in locating the cusp chart inside the generic fibre.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_IgusaScheme_exists_iso_glued_pullback_igusaTo_of_algEquiv_chartAlg_chartRing.lean

import Mathlib
import Definitions.Def_ModularCurve_IgusaScheme
import Definitions.Def_ModularCurve_X0ModL
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_AlgebraicCurve_CurveModelConstruction

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ModularCurve AlgebraicCurve ModularCurve.IgusaScheme

open scoped TensorProduct

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem ModularCurve.IgusaScheme.exists_iso_glued_pullback_igusaTo_of_algEquiv_chartAlg_chartRing
    (N : ℕ) [NeZero N] (ℓ : ℕ) [Fact ℓ.Prime]
    (K : Type) [Field K] [Algebra ↥(GaloisRep.ratLocalizedAt ℓ) K]
    {L : Type} [Field L] [Algebra K L] (t : L) [Fact (t ≠ 0)]
    (eFin : K ⊗[↥(GaloisRep.ratLocalizedAt ℓ)] ↥(chartAlgFin N ℓ) ≃ₐ[K]
      ↥(AlgebraicCurve.CurveModel.chartRing K ({t} : Set L)))
    (eInf : K ⊗[↥(GaloisRep.ratLocalizedAt ℓ)] ↥(chartAlgInf N ℓ) ≃ₐ[K]
      ↥(AlgebraicCurve.CurveModel.chartRing K ({t⁻¹} : Set L)))
    (hj : ((eFin ((1 : K) ⊗ₜ[↥(GaloisRep.ratLocalizedAt ℓ)] jChartFin N ℓ)) : L) = t)
    (hjInv : ((eInf ((1 : K) ⊗ₜ[↥(GaloisRep.ratLocalizedAt ℓ)] jInvChartInf N ℓ)) : L) = t⁻¹)
    (hcompat : ∀ (b : ↥(chartAlgFin N ℓ)) (b' : ↥(chartAlgInf N ℓ)) (n : ℕ),
      ((b : ↥(modularFunctionFieldFull N)) = (b' : ↥(modularFunctionFieldFull N)) * jFull N ^ n) →
      ((eFin ((1 : K) ⊗ₜ[↥(GaloisRep.ratLocalizedAt ℓ)] b) : L) =
        (eInf ((1 : K) ⊗ₜ[↥(GaloisRep.ratLocalizedAt ℓ)] b') : L) * t ^ n)) :
    ∃ (es : AlgebraicCurve.CurveModel.glued K t ⟶ pullback (igusaTo N ℓ) (Spec.map (CommRingCat.ofHom
        (algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) K)))) (_ : IsIso es),
      es ≫ pullback.snd (igusaTo N ℓ) _ = AlgebraicCurve.CurveModel.gluedToBase K t ∧
      (AlgebraicCurve.CurveModel.ι₀ K t ≫ es ≫ pullback.fst (igusaTo N ℓ) _ =
        Spec.map (CommRingCat.ofHom (eFin.toAlgHom.toRingHom.comp
          (Algebra.TensorProduct.includeRight
            (R := ↥(GaloisRep.ratLocalizedAt ℓ)) (A := K) (B := ↥(chartAlgFin N ℓ))).toRingHom)) ≫
          ModularCurve.IgusaScheme.ιFin N ℓ) ∧
      (AlgebraicCurve.CurveModel.ιInf K t ≫ es ≫ pullback.fst (igusaTo N ℓ) _ =
        Spec.map (CommRingCat.ofHom (eInf.toAlgHom.toRingHom.comp
          (Algebra.TensorProduct.includeRight
            (R := ↥(GaloisRep.ratLocalizedAt ℓ)) (A := K) (B := ↥(chartAlgInf N ℓ))).toRingHom)) ≫
          ModularCurve.IgusaScheme.ιInf N ℓ) := by sorry
