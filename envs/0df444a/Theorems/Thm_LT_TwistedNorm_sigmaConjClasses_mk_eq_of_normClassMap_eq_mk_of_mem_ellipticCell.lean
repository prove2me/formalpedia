-- Prove2me | Theorems.Thm_LT_TwistedNorm_sigmaConjClasses_mk_eq_of_normClassMap_eq_mk_of_mem_ellipticCell
-- name    : LT.TwistedNorm.sigmaConjClasses_mk_eq_of_normClassMap_eq_mk_of_mem_ellipticCell
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:00.858323+00:00
-- url     : https://prove2.me/theorems/8783123c-3d86-597d-9108-c08b586eaf0f
-- title:
--   Injectivity of the twisted norm map on elliptic classes
-- statement:
--   Let $F$ and $L$ be fields with $L$ a finite-dimensional Galois extension of $F$, and let $\sigma$ be an $F$-algebra automorphism of $L$ such that every $F$-algebra automorphism $\tau$ of $L$ lies in `Subgroup.zpowers σ`, i.e. $\sigma$ generates $\mathrm{Gal}(L/F)$ (hypothesis `hgen`). Let $\gamma \in GL_2(F)$ lie in [`AutomorphicForm.ellipticCell F`](def/AutomorphicForm_GL2ConjugacyCells.html#L35), that is, the underlying $2\times 2$ matrix of $\gamma$ satisfies `IsEllipticType`: its characteristic polynomial has no root in $F$. Let $\delta_1, \delta_2 \in GL_2(L)$. On $GL_2(L)$ consider the equivalence relation [`AutomorphicForm.IsSigmaConj`](def/AutomorphicForm_SigmaConjugacy.html#L15) attached to $\sigma$ — $\sigma$-twisted conjugacy, which by `isSigmaConj_iff_exists_eq_inv_mul_mul_map` amounts to the existence of $k \in GL_2(L)$ with $\delta_2 = k^{-1}\delta_1\,\sigma(k)$ — and write `SigmaConjClasses.mk σ δ` for the class of $\delta$ in the quotient. The map `normClassMap hgen` sends such a class to the $GL_2(F)$-conjugacy class of `normRep hgen δ`, the element of $GL_2(F)$ chosen by `exists_map_eq_conj_sigmaNormPow` as a norm representative of $\delta$; this is independent of the representative. Assuming that both $\sigma$-classes are sent by `normClassMap hgen` to the conjugacy class of $\gamma$, the conclusion is that the two $\sigma$-conjugacy classes agree, i.e. $\delta_1$ and $\delta_2$ are $\sigma$-conjugate.
--
--   This is the injectivity, over the elliptic locus, of the norm map from $\sigma$-twisted conjugacy classes in $GL_2(L)$ to conjugacy classes in $GL_2(F)$ for a cyclic extension $L/F$, the step which matches twisted conjugacy classes with elliptic norm against ordinary elliptic conjugacy classes. It is used in the comparison of the geometric sides of the twisted and ordinary trace formulae, in [`LT.TwistedNorm.finsum_inv_card_mul_eq_finsum_inv_card_mul_of_normClassMap_eq_of_mem_ellipticCell`](thm.html#LT.TwistedNorm.finsum_inv_card_mul_eq_finsum_inv_card_mul_of_normClassMap_eq_of_mem_ellipticCell) and in [`AutomorphicForm.finite_sep_exists_twistedKernelSummand_ne_zero_of_hasCompactSupport`](thm.html#AutomorphicForm.finite_sep_exists_twistedKernelSummand_ne_zero_of_hasCompactSupport).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LT_TwistedNorm_sigmaConjClasses_mk_eq_of_normClassMap_eq_mk_of_mem_ellipticCell.lean

import Definitions.Def_TwistedNormClasses
import Definitions.Def_AutomorphicForm_GL2ConjugacyCells

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem LT.TwistedNorm.sigmaConjClasses_mk_eq_of_normClassMap_eq_mk_of_mem_ellipticCell
    {F L : Type*} [Field F] [Field L] [Algebra F L] [FiniteDimensional F L] [IsGalois F L]
    {σ : L ≃ₐ[F] L} (hgen : ∀ τ : L ≃ₐ[F] L, τ ∈ Subgroup.zpowers σ)
    (γ : Matrix.GeneralLinearGroup (Fin 2) F) (hγ : γ ∈ AutomorphicForm.ellipticCell F)
    (δ₁ δ₂ : Matrix.GeneralLinearGroup (Fin 2) L)
    (h₁ : LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ δ₁) = ConjClasses.mk γ)
    (h₂ : LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ δ₂) = ConjClasses.mk γ) :
    LT.TwistedNorm.SigmaConjClasses.mk σ δ₁ = LT.TwistedNorm.SigmaConjClasses.mk σ δ₂ := by sorry
