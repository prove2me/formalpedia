-- Prove2me | Theorems.Thm_ModularCurve_IgusaScheme_exists_algHom_tensor_chartAlg_injective_isIntegrallyClosed
-- name    : ModularCurve.IgusaScheme.exists_algHom_tensor_chartAlg_injective_isIntegrallyClosed
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:39.1924+00:00
-- url     : https://prove2.me/theorems/f9057b57-f68d-5816-af62-99c17deb726a
-- title:
--   Base change of Igusa chart rings to a place over ℓ ∤ N
-- statement:
--   Fix a nonzero natural number $N$ and a prime $\ell$ with $\ell \nmid N$. Let $A$ be a valuation subring of $\overline{\mathbb Q} =$ `AlgebraicClosure ℚ` lying over $\ell$ in the sense that the image of $\ell$ is a nonunit of $A$, and let $\rho$ be a ring homomorphism from $\mathbb Z_{(\ell)} =$ [`GaloisRep.ratLocalizedAt ℓ`](def/GaloisRep_Flat.html#L8), the subring of rationals whose denominator is coprime to $\ell$, into $A$ whose composite with the inclusion $A \hookrightarrow \overline{\mathbb Q}$ is the canonical map; thus $A$ is a $\mathbb Z_{(\ell)}$-algebra via $\rho$. Write $F =$ `modularFunctionFieldFull N` for the subfield of $\mathbb Q((q))$ generated over $\mathbb Q$ by the expansions $j(q^d)$ for the nonzero divisors $d$ of $N$, and $\overline{\mathbb Q}\cdot F =$ `laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N)` for the subfield of $\overline{\mathbb Q}((q))$ generated over $\overline{\mathbb Q}$ by the coefficientwise image of $F$; the latter is an $A$-algebra through `constantsHom N A`, the inclusion $A \subseteq \overline{\mathbb Q}$ followed by the constants. Let $B_{\mathrm{fin}} =$ `chartAlgFin N ℓ` and $B_\infty =$ `chartAlgInf N ℓ` be the subalgebras of $F$ of elements integral over $\mathbb Z_{(\ell)}[j]$, respectively over $\mathbb Z_{(\ell)}[j^{-1}]$. The assertion is, for each of $B = B_{\mathrm{fin}}$ and $B = B_\infty$: there is an $A$-algebra homomorphism $\psi : A \otimes_{\mathbb Z_{(\ell)}} B \to \overline{\mathbb Q}\cdot F$ with $\psi(a \otimes b)$ equal, as a Laurent series over $\overline{\mathbb Q}$, to the product of $a$ with the coefficientwise image of the series $b$, such that $\psi$ is injective and its range is an integrally closed domain.
--
--   This is the normality of the affine charts of the Igusa model of $X_0(N)$ after base change to a place of $\overline{\mathbb Q}$ above $\ell \nmid N$, together with the statement that normalisation commutes with that base change: the image of $\psi$ is the integral closure of $A[j]$ (respectively $A[j^{-1}]$) inside $\overline{\mathbb Q}\cdot F$. It is used in the identification of the residue-field fibres of the chart rings and in the description of the chart algebras by generators.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_IgusaScheme_exists_algHom_tensor_chartAlg_injective_isIntegrallyClosed.lean

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
open IsLocalRing ModularCurve ModularCurve.IgusaScheme ModularCurve.CharPModel AlgebraicCurve

theorem ModularCurve.IgusaScheme.exists_algHom_tensor_chartAlg_injective_isIntegrallyClosed
    (N : ℕ) [NeZero N] (ℓ : ℕ) [Fact ℓ.Prime] (hℓN : ¬ ℓ ∣ N)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime ℓ)
    (ρ : ↥(GaloisRep.ratLocalizedAt ℓ) →+* ↥A)
    (hρ : A.subtype.comp ρ = algebraMap ↥(GaloisRep.ratLocalizedAt ℓ) (AlgebraicClosure ℚ)) :
    letI := ρ.toAlgebra
    letI := (constantsHom N A).toAlgebra
    (∃ ψ : ↥A ⊗[↥(GaloisRep.ratLocalizedAt ℓ)] ↥(chartAlgFin N ℓ) →ₐ[↥A]
        laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N),
      (∀ (a : ↥A) (b : ↥(chartAlgFin N ℓ)),
        (ψ (a ⊗ₜ b) : LaurentSeries (AlgebraicClosure ℚ)) =
          (constantsHom N A a : LaurentSeries (AlgebraicClosure ℚ)) *
            coeffEmb (AlgebraicClosure ℚ) ((b : ↥(modularFunctionFieldFull N)) : LaurentSeries ℚ)) ∧
      Function.Injective ψ ∧ IsDomain ↥ψ.range ∧ IsIntegrallyClosed ↥ψ.range) ∧
    (∃ ψ : ↥A ⊗[↥(GaloisRep.ratLocalizedAt ℓ)] ↥(chartAlgInf N ℓ) →ₐ[↥A]
        laurentBaseChange (AlgebraicClosure ℚ) (modularFunctionFieldFull N),
      (∀ (a : ↥A) (b : ↥(chartAlgInf N ℓ)),
        (ψ (a ⊗ₜ b) : LaurentSeries (AlgebraicClosure ℚ)) =
          (constantsHom N A a : LaurentSeries (AlgebraicClosure ℚ)) *
            coeffEmb (AlgebraicClosure ℚ) ((b : ↥(modularFunctionFieldFull N)) : LaurentSeries ℚ)) ∧
      Function.Injective ψ ∧ IsDomain ↥ψ.range ∧ IsIntegrallyClosed ↥ψ.range) := by sorry
