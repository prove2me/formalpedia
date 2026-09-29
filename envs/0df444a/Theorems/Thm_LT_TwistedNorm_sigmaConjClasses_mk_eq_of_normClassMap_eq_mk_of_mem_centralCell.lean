-- Prove2me | Theorems.Thm_LT_TwistedNorm_sigmaConjClasses_mk_eq_of_normClassMap_eq_mk_of_mem_centralCell
-- name    : LT.TwistedNorm.sigmaConjClasses_mk_eq_of_normClassMap_eq_mk_of_mem_centralCell
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:00.858323+00:00
-- url     : https://prove2.me/theorems/3c0b31a6-b3e5-584a-a3c5-3c39903adad4
-- title:
--   Injectivity of the twisted norm map over central classes
-- statement:
--   Let $F$ and $L$ be fields with $L$ an $F$-algebra, $L/F$ finite and Galois, and $F$ infinite. Let $\sigma$ be an $F$-algebra automorphism of $L$ such that every $\tau \in \mathrm{Gal}(L/F)$ lies in the subgroup of integer powers of $\sigma$, so that the Galois group is cyclic with generator $\sigma$. Let $\gamma \in GL_2(F)$ lie in [`AutomorphicForm.centralCell F`](def/AutomorphicForm_GL2ConjugacyCells.html#L26), i.e. the underlying matrix of $\gamma$ is $c \cdot 1$ for some scalar $c \in F$. Let $\delta_1, \delta_2 \in GL_2(L)$, and suppose that the twisted norm class map [`LT.TwistedNorm.normClassMap hgen`](def/TwistedNormClasses.html#L766), which sends the $\sigma$-conjugacy class of a $\delta$ to the $GL_2(F)$-conjugacy class of its chosen base-field norm representative [`LT.TwistedNorm.normRep hgen δ`](def/TwistedNormClasses.html#L746), takes the class of $\delta_1$ and the class of $\delta_2$ both to the conjugacy class of $\gamma$. Then the classes of $\delta_1$ and $\delta_2$ in [`LT.TwistedNorm.SigmaConjClasses σ`](def/TwistedNormClasses.html#L716) coincide: $\delta_1$ and $\delta_2$ are $\sigma$-conjugate, i.e. $\delta_2 = k^{-1} \delta_1 \sigma(k)$ for some $k \in GL_2(L)$.
--
--   This is the injectivity of the norm map from $\sigma$-conjugacy classes in $GL_2(L)$ to conjugacy classes in $GL_2(F)$, restricted to the classes whose norm class is that of a scalar matrix; it is the central-element half of Langlands's lemma on twisted classes with elliptic or central norm in cyclic base change for $GL(2)$. It is used in the analysis of twisted kernel summands for compactly supported data and in the extraction of an explicit scalar multiple $k^{-1}\delta_1\sigma(k)$ from equality of norm classes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LT_TwistedNorm_sigmaConjClasses_mk_eq_of_normClassMap_eq_mk_of_mem_centralCell.lean

import Definitions.Def_TwistedNormClasses
import Definitions.Def_AutomorphicForm_GL2ConjugacyCells

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem LT.TwistedNorm.sigmaConjClasses_mk_eq_of_normClassMap_eq_mk_of_mem_centralCell
    {F L : Type*} [Field F] [Field L] [Algebra F L] [FiniteDimensional F L] [IsGalois F L]
    [Infinite F]
    {σ : L ≃ₐ[F] L} (hgen : ∀ τ : L ≃ₐ[F] L, τ ∈ Subgroup.zpowers σ)
    (γ : Matrix.GeneralLinearGroup (Fin 2) F) (hγ : γ ∈ AutomorphicForm.centralCell F)
    (δ₁ δ₂ : Matrix.GeneralLinearGroup (Fin 2) L)
    (h₁ : LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ δ₁) = ConjClasses.mk γ)
    (h₂ : LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ δ₂) = ConjClasses.mk γ) :
    LT.TwistedNorm.SigmaConjClasses.mk σ δ₁ = LT.TwistedNorm.SigmaConjClasses.mk σ δ₂ := by sorry
