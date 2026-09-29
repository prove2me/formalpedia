-- Prove2me | Theorems.Thm_IsFractionRing_bijective_tensorProduct_lift_of_bijective_baseChange
-- name    : IsFractionRing.bijective_tensorProduct_lift_of_bijective_baseChange
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.878306+00:00
-- url     : https://prove2.me/theorems/083cc5eb-7f42-5e6f-94a8-ac38e21c98ca
-- title:
--   Fraction fields of a bijective base change
-- statement:
--   Let $R$, $S$, $\widehat R$, $T$ be commutative domains and $K_1$, $K$, $E$, $F$ fields, arranged as follows. $S$ is an $R$-algebra which is finite as an $R$-module and has no zero smul-divisors over $R$; $K_1$ is a fraction field of $R$ and $K$ a fraction field of $S$, with $K$ an $R$- and $K_1$-algebra making the towers $R \to S \to K$ and $R \to K_1 \to K$ compatible. Further, $\widehat R$ is an $R$-algebra, $E$ is a fraction field of $\widehat R$, and $E$ carries compatible $R$- and $K_1$-algebra structures via the towers $R \to \widehat R \to E$ and $R \to K_1 \to E$. Finally $T$ is simultaneously an $\widehat R$-, $S$- and $R$-algebra with compatible towers, and the hypothesis $hT$ asserts that the canonical $\widehat R$-algebra map $\widehat R \otimes_R S \to T$ determined by the structure map $\widehat R \to T$ and by $S \to T$ is bijective; $F$ is a fraction field of $T$, equipped with $E$-, $\widehat R$-, $K$-, $S$- and $K_1$-algebra structures making all the evident towers ($\widehat R \to E \to F$, $\widehat R \to T \to F$, $S \to K \to F$, $S \to T \to F$, $K_1 \to E \to F$, $K_1 \to K \to F$) compatible. The conclusion is that the canonical $E$-algebra map $E \otimes_{K_1} K \to F$ determined by $E \to F$ and $K \to F$ is again bijective.
--
--   This is the passage from a bijective base change of domains to the corresponding statement for their fraction fields: if $T \cong \widehat R \otimes_R S$ then $\operatorname{Frac} T \cong \operatorname{Frac}(\widehat R) \otimes_{K_1} K$. It is used in the analysis of the completed local rings of a model of a modular curve at a point, where $\widehat R$ is a completion of $R$ and $T$ the completed local ring upstairs, to identify the residue field extension data needed for the Galois descent step.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsFractionRing_bijective_tensorProduct_lift_of_bijective_baseChange.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct

theorem IsFractionRing.bijective_tensorProduct_lift_of_bijective_baseChange
    {R S Rhat T K₁ K E F : Type*}
    [CommRing R] [IsDomain R] [CommRing S] [IsDomain S] [CommRing Rhat] [IsDomain Rhat]
    [CommRing T] [IsDomain T] [Field K₁] [Field K] [Field E] [Field F]

    [Algebra R S] [Module.Finite R S] [NoZeroSMulDivisors R S]
    [Algebra R K₁] [IsFractionRing R K₁] [Algebra S K] [IsFractionRing S K]
    [Algebra R K] [Algebra K₁ K] [IsScalarTower R S K] [IsScalarTower R K₁ K]

    [Algebra R Rhat] [Algebra Rhat E] [IsFractionRing Rhat E]
    [Algebra R E] [Algebra K₁ E] [IsScalarTower R Rhat E] [IsScalarTower R K₁ E]

    [Algebra Rhat T] [Algebra S T] [Algebra R T] [IsScalarTower R Rhat T] [IsScalarTower R S T]
    (hT : Function.Bijective
      (Algebra.TensorProduct.lift (Algebra.ofId Rhat T) (IsScalarTower.toAlgHom R S T)
        (fun _ _ => Commute.all _ _) : Rhat ⊗[R] S →ₐ[Rhat] T))
    [Algebra T F] [IsFractionRing T F]

    [Algebra E F] [Algebra Rhat F] [IsScalarTower Rhat E F] [IsScalarTower Rhat T F]
    [Algebra K F] [Algebra S F] [IsScalarTower S K F] [IsScalarTower S T F]
    [Algebra K₁ F] [IsScalarTower K₁ E F] [IsScalarTower K₁ K F] :
    Function.Bijective
      (Algebra.TensorProduct.lift (Algebra.ofId E F) (IsScalarTower.toAlgHom K₁ K F)
        (fun _ _ => Commute.all _ _) : E ⊗[K₁] K →ₐ[E] F) := by sorry
