-- Prove2me | Theorems.Thm_ModularCurve_heckePic0Fibre_eq_neg_fricke_smul_of_prime
-- name    : ModularCurve.heckePic0Fibre_eq_neg_fricke_smul_of_prime
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.700479+00:00
-- url     : https://prove2.me/theorems/e866b30a-f377-56ae-810b-9d056ab6cce6
-- title:
--   Uₚ=-wₚ on Pic⁰ of the special fibre
-- statement:
--   Let $p$ and $\ell$ be primes with $\ell \nmid p$, and let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ lying over $\ell$ in the sense that the image of $\ell$ lies in the non-units of $A$; write $k = \mathrm{ResidueField}(A)$. Assume the hypothesis `hE` that the two intermediate fields of $k((q))$ coincide: $\mathrm{modularFunctionFieldC}\,k\,p$, generated over $k$ by `jqModC` and `jqNModC`, equals $\mathrm{modularFunctionFieldFullC}\,k\,p$, generated over $k$ by the family `divisorExpansionsC`. Let $\tau$ be a $k$-algebra automorphism of $\mathrm{modularFunctionFieldFullC}\,k\,p$ interchanging the element `jqModC k` with its $p$-fold $q$-substitution $\mathrm{qExpand}\,k\,p(\mathrm{jqModC}\,k)$, in both directions (hypotheses $h\tau_1$, $h\tau_2$). Let $y$ be an element of $\mathrm{JZeroC}\,k\,p = \mathrm{Pic}^0$ of $\mathrm{modularFunctionFieldFullC}\,k\,p$ over $k$, that is, degree-zero divisors on the places of this function field modulo principal divisors. Then transporting $y$ backwards along the isomorphism of $\mathrm{Pic}^0$ groups induced by the field identification `hE`, applying $\mathrm{heckePic0Fibre}\,k\,p\,p$ (the $\mathbb{Z}$-linear endomorphism attached to the divisor correspondence `heckeDivFibre` when `HeckeInputsFibre k p p` holds, and $0$ otherwise), and transporting forwards again gives $-(\tau \cdot y)$, where $\tau$ acts on $\mathrm{Pic}^0$ by transport of places.
--
--   This is the identity $U_p = -w_p$ on the degree-zero divisor class group of the function field of the special fibre of $X_0(p)$ at a prime $\ell \neq p$, the characteristic-$\ell$ reduction of the relation $U_p + w_p = 0$ on $J_0(p)$ available at prime level. It is used in the analysis of the kernel of the Eisenstein ideal on the special fibre, namely in [`ModularCurve.exists_nsmul_generator_heckeTorsion_span_sup_of_reductionModL_eisensteinMaximalIdeal_smul_eq_zero`](thm.html#ModularCurve.exists_nsmul_generator_heckeTorsion_span_sup_of_reductionModL_eisensteinMaximalIdeal_smul_eq_zero).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_heckePic0Fibre_eq_neg_fricke_smul_of_prime.lean

import Mathlib
import Definitions.Def_ModularCurve_ReductionModL
import Definitions.Def_ModularCurve_CharLDegeneracyHecke
import Definitions.Def_AlgebraicCurve_Pic0Congr
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve AlgebraicCurve
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1600000 in

theorem ModularCurve.heckePic0Fibre_eq_neg_fricke_smul_of_prime
    (p : ℕ) [Fact p.Prime] {ℓ : ℕ} [Fact ℓ.Prime] (hℓp : ¬ ℓ ∣ p)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime ℓ)
    (hE : modularFunctionFieldC (IsLocalRing.ResidueField A) p =
      modularFunctionFieldFullC (IsLocalRing.ResidueField A) p)
    (τ : modularFunctionFieldFullC (IsLocalRing.ResidueField A) p ≃ₐ[IsLocalRing.ResidueField A]
      modularFunctionFieldFullC (IsLocalRing.ResidueField A) p)
    (hτ₁ : τ ⟨jqModC (IsLocalRing.ResidueField A), jqModC_mem_full (IsLocalRing.ResidueField A) p⟩ =
      ⟨qExpand (IsLocalRing.ResidueField A) p (jqModC (IsLocalRing.ResidueField A)),
        jqModCd_mem_full (IsLocalRing.ResidueField A) p dvd_rfl⟩)
    (hτ₂ : τ ⟨qExpand (IsLocalRing.ResidueField A) p (jqModC (IsLocalRing.ResidueField A)),
        jqModCd_mem_full (IsLocalRing.ResidueField A) p dvd_rfl⟩ =
      ⟨jqModC (IsLocalRing.ResidueField A), jqModC_mem_full (IsLocalRing.ResidueField A) p⟩)
    (y : JZeroC (IsLocalRing.ResidueField A) p) :
    Pic0.congr (IntermediateField.equivOfEq hE).toRingEquiv
        (fun a => (IntermediateField.equivOfEq hE).commutes a)
        (heckePic0Fibre (IsLocalRing.ResidueField A) p p
          ((Pic0.congr (IntermediateField.equivOfEq hE).toRingEquiv
            (fun a => (IntermediateField.equivOfEq hE).commutes a)).symm y)) = -(τ • y) := by sorry
