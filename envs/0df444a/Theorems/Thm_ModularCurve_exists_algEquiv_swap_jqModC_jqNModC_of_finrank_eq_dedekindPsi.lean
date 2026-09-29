-- Prove2me | Theorems.Thm_ModularCurve_exists_algEquiv_swap_jqModC_jqNModC_of_finrank_eq_dedekindPsi
-- name    : ModularCurve.exists_algEquiv_swap_jqModC_jqNModC_of_finrank_eq_dedekindPsi
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.209688+00:00
-- url     : https://prove2.me/theorems/4224f380-652c-57ae-b24a-6aad4d62b612
-- title:
--   Automorphism of K(̄ j,̄ j_ℓ) swapping ̄ j and ̄ j_ℓ
-- statement:
--   Let $K$ be a field and $\ell$ a prime. Inside the field of formal Laurent series $K((q))$ consider the element $\bar j =$ `jqModC K`, namely $q^{-1}$ times the image in $K[[q]]$ of the integral power series `jNum` $= E_4^3\cdot$ `dedekindEtaUnitInv` (the $q$-expansion of the modular invariant $j$), and its image $\bar j_\ell =$ `jqNModC K ℓ` under the ring homomorphism `qExpand K ℓ`, which multiplies all Laurent exponents by $\ell$, i.e. substitutes $q \mapsto q^{\ell}$. The hypothesis is that the intermediate field obtained by adjoining $\bar j_\ell$ to $K(\bar j)$ inside $K((q))$ has dimension exactly `dedekindPsi ℓ` $= \sum_{d \mid \ell,\ d \text{ squarefree}} \ell/d$ as a module over $K(\bar j)$, where $K(\bar j)$ denotes the $K$-subalgebra-generated intermediate field `IntermediateField.adjoin K {jqModC K}`. Under this hypothesis there exists a $K$-algebra automorphism $\sigma$ of the modular function field `modularFunctionFieldC K ℓ` $= K(\bar j, \bar j_\ell) \subseteq K((q))$ which interchanges the two distinguished generators: $\sigma$ carries $\bar j$ (with its membership witness) to $\bar j_\ell$ and $\bar j_\ell$ to $\bar j$.
--
--   This is the function-field form of the Fricke involution $W_\ell$ of $X_0(\ell)$, obtained from the symmetry of the modular polynomial $\Phi_\ell(X,Y) = \Phi_\ell(Y,X)$: once the relative degree $[K(\bar j,\bar j_\ell):K(\bar j)]$ attains the full value $\psi(\ell) = \ell + 1$, the exchange of the two generators respects the single relation between them and so extends to a $K$-automorphism. It is used in the study of Hecke torsion, being cited by [`ModularCurve.exists_nsmul_generator_heckeTorsion_span_sup_of_reductionModL_eisensteinMaximalIdeal_smul_eq_zero`](thm.html#ModularCurve.exists_nsmul_generator_heckeTorsion_span_sup_of_reductionModL_eisensteinMaximalIdeal_smul_eq_zero).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_algEquiv_swap_jqModC_jqNModC_of_finrank_eq_dedekindPsi.lean

import Definitions.Def_ModularCurve_JqCoeff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve

theorem ModularCurve.exists_algEquiv_swap_jqModC_jqNModC_of_finrank_eq_dedekindPsi (K : Type*) [Field K] (ℓ : ℕ) [Fact ℓ.Prime]
    (hdeg : Module.finrank (IntermediateField.adjoin K ({jqModC K} : Set (LaurentSeries K)))
      (IntermediateField.adjoin (IntermediateField.adjoin K ({jqModC K} : Set (LaurentSeries K)))
        ({jqNModC K ℓ} : Set (LaurentSeries K))) = dedekindPsi ℓ) :
    ∃ σ : modularFunctionFieldC K ℓ ≃ₐ[K] modularFunctionFieldC K ℓ,
      σ ⟨jqModC K, jqModC_mem K ℓ⟩ = ⟨jqNModC K ℓ, jqNModC_mem K ℓ⟩ ∧
      σ ⟨jqNModC K ℓ, jqNModC_mem K ℓ⟩ = ⟨jqModC K, jqModC_mem K ℓ⟩ := by sorry
