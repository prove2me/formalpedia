-- Prove2me | Theorems.Thm_Module_Flat_exists_fg_subalgebra_flat_localization_tensorProduct
-- name    : Module.Flat.exists_fg_subalgebra_flat_localization_tensorProduct
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.610395+00:00
-- url     : https://prove2.me/theorems/89403d9e-b279-5d54-8077-eb541d858611
-- title:
--   Descent of flatness at a prime to a finitely generated subalgebra
-- statement:
--   Let $R_0$ be a Noetherian commutative ring, let $R$ be a commutative $R_0$-algebra (arbitrary), and let $B_0$ be a commutative $R_0$-algebra of finite type. Let $P$ be a prime ideal of $R \otimes_{R_0} B_0$ and assume that the localisation $(R \otimes_{R_0} B_0)_P$ is flat as an $R$-module. The conclusion asserts the existence of an $R_0$-subalgebra $R_1 \subseteq R$ which is finitely generated as an $R_0$-algebra and has the following property: let $\varphi \colon R_1 \otimes_{R_0} B_0 \to R \otimes_{R_0} B_0$ be the ring homomorphism underlying the tensor product of the inclusion $R_1 \hookrightarrow R$ with the identity of $B_0$, and let $P_1 = \varphi^{-1}(P)$, a prime ideal of $R_1 \otimes_{R_0} B_0$; then the localisation $(R_1 \otimes_{R_0} B_0)_{P_1}$ is flat as an $R_1$-module. Thus flatness of the local ring at $P$ over the base already holds over a finitely generated stage of $R$, for the single prime $P$ given.
--
--   This is the pointwise form, at one prime, of the descent of flatness along the filtered union of the finitely generated $R_0$-subalgebras of $R$, as in EGA IV$_3$, 11.2.6. It feeds the global statement [`Module.Flat.exists_fg_subalgebra_flat_tensorProduct`](thm.html#Module.Flat.exists_fg_subalgebra_flat_tensorProduct) and the criterion [`Module.Flat.of_finitePresentation_of_forall_flat_residueField_tensorProduct`](thm.html#Module.Flat.of_finitePresentation_of_forall_flat_residueField_tensorProduct), which are used in the commutative-algebra input to the deformation-theoretic part of the argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Module_Flat_exists_fg_subalgebra_flat_localization_tensorProduct.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open TensorProduct

theorem Module.Flat.exists_fg_subalgebra_flat_localization_tensorProduct
    {R₀ R B₀ : Type*} [CommRing R₀] [CommRing R] [CommRing B₀]
    [Algebra R₀ R] [Algebra R₀ B₀] [IsNoetherianRing R₀] [Algebra.FiniteType R₀ B₀]
    (P : Ideal (R ⊗[R₀] B₀)) [P.IsPrime]
    [Module.Flat R (Localization.AtPrime P)] :
    ∃ R₁ : Subalgebra R₀ R, R₁.FG ∧
      Module.Flat R₁ (Localization.AtPrime
        (P.comap (Algebra.TensorProduct.map R₁.val (AlgHom.id R₀ B₀)).toRingHom)) := by sorry
