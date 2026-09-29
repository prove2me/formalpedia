-- Prove2me | Theorems.Thm_ModularCurve_IgusaScheme_exists_algEquiv_residueField_tensor_chartAlg_chartRing_apply_tmul
-- name    : ModularCurve.IgusaScheme.exists_algEquiv_residueField_tensor_chartAlg_chartRing_apply_tmul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:39.1924+00:00
-- url     : https://prove2.me/theorems/3b864189-8002-5230-944e-12ed71b0376e
-- title:
--   Special fibres of the Igusa charts as characteristic-ℓ chart rings
-- statement:
--   Let $N\ge 1$, let $\ell$ be a prime with $\ell\nmid N$, and let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ lying over $\ell$ in the sense that the image of $\ell$ lies in the nonunits of $A$, whose residue field $\kappa=\mathrm{ResidueField}\,A$ is of characteristic $\ell$ and algebraically closed. Let $\rho\colon \mathbb{Z}_{(\ell)}\to A$ be a ring homomorphism from the subring $\mathbb{Z}_{(\ell)}$ of rationals whose denominator is coprime to $\ell$, compatible with the inclusion $A\subseteq\overline{\mathbb{Q}}$, and let $fm$ be a fibre model of level $N$ over $A$ with reduction $A\to\kappa$: a pair of subrings $B_{\mathrm{fin}},B_\infty$ of the compositum $\overline{\mathbb{Q}}\cdot F_N$ inside $\overline{\mathbb{Q}}((q))$ (where $F_N$ is the field generated over $\mathbb{Q}$ by the divisor $q$-expansions of level $N$), containing the constants from $A$ and $\bar\jmath,\bar\jmath_N$ resp.\ $\bar\jmath^{-1}$, integral over the respective affine bases, together with reduction homomorphisms $\pi_{\mathrm{fin}},\pi_\infty$ to $\kappa(\tilde\jmath,\tilde\jmath_N)\subseteq\kappa((q))$ normalising constants, $\bar\jmath$, $\bar\jmath_N$ and $\bar\jmath^{-1}$. Assume the coefficientwise images of the Igusa chart algebras $\mathcal{O}_{\mathrm{fin}}=\mathrm{chartAlg}\,N\,\ell\,\{j\}$ and $\mathcal{O}_\infty=\mathrm{chartAlg}\,N\,\ell\,\{j^{-1}\}$ lie in $B_{\mathrm{fin}}$ and $B_\infty$ respectively. Then, with $\kappa$ a $\mathbb{Z}_{(\ell)}$-algebra via $\rho$ followed by reduction, there exist $\kappa$-algebra isomorphisms $e_{\mathrm{fin}}\colon \kappa\otimes_{\mathbb{Z}_{(\ell)}}\mathcal{O}_{\mathrm{fin}}\to \mathrm{chartRing}_\kappa\{\tilde\jmath\}$ and $e_\infty\colon \kappa\otimes_{\mathbb{Z}_{(\ell)}}\mathcal{O}_\infty\to \mathrm{chartRing}_\kappa\{\tilde\jmath^{-1}\}$ onto the sets of elements of $\kappa$-adjoin of the divisor $q$-expansions in characteristic $\ell$ that are integral over $\kappa[\tilde\jmath]$, resp.\ $\kappa[\tilde\jmath^{-1}]$, such that on pure tensors the underlying Laurent series satisfy $e_{\mathrm{fin}}(x\otimes b)=x\cdot\pi_{\mathrm{fin}}(b)$ and $e_\infty(x\otimes b)=x\cdot\pi_\infty(b)$ for all $x\in\kappa$.
--
--   This is the explicit-maps form of the good reduction of $X_0(N)$ at a prime $\ell\nmid N$: each of the two charts of the Igusa scheme has special fibre the corresponding chart ring of Igusa's curve over $\kappa$, and the identification is induced by reduction of $q$-expansions through the given fibre model, which pins the isomorphisms down on all pure tensors rather than only on $j$ and $j^{-1}$. It feeds the compatibility statement for the two chart isomorphisms and the construction of the cusp chart and base data for the generic-fibre identification.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_IgusaScheme_exists_algEquiv_residueField_tensor_chartAlg_chartRing_apply_tmul.lean

import Mathlib
import Definitions.Def_ModularCurve_IgusaScheme
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_ModularCurve_X0ModL
import Definitions.Def_ModularCurve_FibreModel
import Definitions.Def_JacJ1_ChartAlgebra

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped TensorProduct
open IsLocalRing ModularCurve ModularCurve.IgusaScheme ModularCurve.CharPModel
open AlgebraicCurve hiding CurveModel

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem ModularCurve.IgusaScheme.exists_algEquiv_residueField_tensor_chartAlg_chartRing_apply_tmul
    (N : ℕ) [NeZero N] (ℓ : ℕ) [Fact ℓ.Prime] (hℓN : ¬ ℓ ∣ N)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime ℓ)
    [CharP (ResidueField ↥A) ℓ] [IsAlgClosed (ResidueField ↥A)]
    (ρ : ↥(GaloisRep.ratLocalizedAt ℓ) →+* ↥A)
    (hρ : A.subtype.comp ρ = algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) (AlgebraicClosure ℚ))
    (fm : CharPModel.FibreModel N A ℓ (ResidueField ↥A) (residue ↥A))
    (hsubF : ∀ b : ↥(chartAlgFin N ℓ),
      (⟨coeffEmb (AlgebraicClosure ℚ) ((b : ↥(modularFunctionFieldFull N)) : LaurentSeries ℚ),
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
          (b : ↥(modularFunctionFieldFull N)).2⟩ :
        laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N)) ∈ fm.BFin)
    (hsubI : ∀ b : ↥(chartAlgInf N ℓ),
      (⟨coeffEmb (AlgebraicClosure ℚ) ((b : ↥(modularFunctionFieldFull N)) : LaurentSeries ℚ),
        coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
          (b : ↥(modularFunctionFieldFull N)).2⟩ :
        laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N)) ∈ fm.BInf) :
    letI := ((residue ↥A).comp ρ).toAlgebra
    (∃ eFin : ResidueField ↥A ⊗[↥(GaloisRep.ratLocalizedAt ℓ)] ↥(chartAlgFin N ℓ) ≃ₐ[ResidueField ↥A]
        ↥(CurveModel.chartRing (ResidueField ↥A)
          ({⟨jqModC (ResidueField ↥A), jqModC_mem_full (ResidueField ↥A) N⟩} :
            Set ↥(modularFunctionFieldFullC (ResidueField ↥A) N))),
      ∀ (x : ResidueField ↥A) (b : ↥(chartAlgFin N ℓ)),
        (((eFin (x ⊗ₜ[↥(GaloisRep.ratLocalizedAt ℓ)] b)).1 : ↥(modularFunctionFieldFullC (ResidueField ↥A) N)) :
            LaurentSeries (ResidueField ↥A)) =
          algebraMap (ResidueField ↥A) (LaurentSeries (ResidueField ↥A)) x *
            ((fm.piFin ⟨_, hsubF b⟩ : ↥(modularFunctionFieldC (ResidueField ↥A) N)) :
              LaurentSeries (ResidueField ↥A))) ∧
    (∃ eInf : ResidueField ↥A ⊗[↥(GaloisRep.ratLocalizedAt ℓ)] ↥(chartAlgInf N ℓ) ≃ₐ[ResidueField ↥A]
        ↥(CurveModel.chartRing (ResidueField ↥A)
          ({(⟨jqModC (ResidueField ↥A), jqModC_mem_full (ResidueField ↥A) N⟩ :
              ↥(modularFunctionFieldFullC (ResidueField ↥A) N))⁻¹} :
            Set ↥(modularFunctionFieldFullC (ResidueField ↥A) N))),
      ∀ (x : ResidueField ↥A) (b : ↥(chartAlgInf N ℓ)),
        (((eInf (x ⊗ₜ[↥(GaloisRep.ratLocalizedAt ℓ)] b)).1 : ↥(modularFunctionFieldFullC (ResidueField ↥A) N)) :
            LaurentSeries (ResidueField ↥A)) =
          algebraMap (ResidueField ↥A) (LaurentSeries (ResidueField ↥A)) x *
            ((fm.piInf ⟨_, hsubI b⟩ : ↥(modularFunctionFieldC (ResidueField ↥A) N)) :
              LaurentSeries (ResidueField ↥A))) := by sorry
