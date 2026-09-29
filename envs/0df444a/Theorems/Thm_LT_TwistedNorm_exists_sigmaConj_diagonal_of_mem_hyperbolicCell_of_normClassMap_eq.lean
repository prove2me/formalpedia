-- Prove2me | Theorems.Thm_LT_TwistedNorm_exists_sigmaConj_diagonal_of_mem_hyperbolicCell_of_normClassMap_eq
-- name    : LT.TwistedNorm.exists_sigmaConj_diagonal_of_mem_hyperbolicCell_of_normClassMap_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:00.858323+00:00
-- url     : https://prove2.me/theorems/28540a5e-c085-5af6-804a-30eaccf8fe42
-- title:
--   Diagonal σ-conjugate when the norm class is hyperbolic
-- statement:
--   Let $F$ and $L$ be fields with $L$ an $F$-algebra that is finite-dimensional and Galois over $F$, and let $\sigma$ be an $F$-algebra automorphism of $L$ such that every $F$-algebra automorphism $\tau$ of $L$ lies in the subgroup of integer powers of $\sigma$ (so $\mathrm{Gal}(L/F)$ is cyclic with generator $\sigma$). Let $\gamma \in GL_2(F)$ lie in [`AutomorphicForm.hyperbolicCell F`](def/AutomorphicForm_GL2ConjugacyCells.html#L32), that is, the characteristic polynomial of the underlying matrix of $\gamma$ factors as $(X - a)(X - b)$ with $a, b \in F$ and $a \neq b$. Let $\delta \in GL_2(L)$ and assume that [`LT.TwistedNorm.normClassMap hgen`](def/TwistedNormClasses.html#L766) sends the class of $\delta$ for the $\sigma$-conjugacy relation on $GL_2(L)$ (the relation [`AutomorphicForm.IsSigmaConj`](def/AutomorphicForm_SigmaConjugacy.html#L15), equivalently $\delta' = k^{-1}\delta\,\sigma(k)$ for some $k$, with $\sigma$ acting entrywise) to the $GL_2(F)$-conjugacy class of $\gamma$; here `normClassMap` is the map induced on $\sigma$-conjugacy classes by passing to the conjugacy class of [`LT.TwistedNorm.normRep hgen δ`](def/TwistedNormClasses.html#L746), the element of $GL_2(F)$ chosen by `exists_map_eq_conj_sigmaNormPow`. The conclusion is that there exists $g \in GL_2(L)$ such that the matrix underlying $g^{-1}\,\delta\,\sigma(g)$ has vanishing $(1,0)$ and $(0,1)$ entries, i.e. is diagonal.
--
--   This is the normalisation step in the twisted-conjugacy theory of $GL_2$ over a cyclic extension: a $\sigma$-conjugacy class whose norm class is regular semisimple split (hyperbolic type) over $F$ contains a diagonal element. It is used in [`LT.TwistedNorm.setOf_exists_mem_center_subset_and_exists_and_eq_iff_of_diagonal`](thm.html#LT.TwistedNorm.setOf_exists_mem_center_subset_and_exists_and_eq_iff_of_diagonal), where $\sigma$-conjugacy classes are compared with sets of diagonal representatives.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LT_TwistedNorm_exists_sigmaConj_diagonal_of_mem_hyperbolicCell_of_normClassMap_eq.lean

import Definitions.Def_TwistedNormClasses
import Definitions.Def_AutomorphicForm_GL2ConjugacyCells

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem LT.TwistedNorm.exists_sigmaConj_diagonal_of_mem_hyperbolicCell_of_normClassMap_eq
    {F L : Type*} [Field F] [Field L] [Algebra F L] [FiniteDimensional F L] [IsGalois F L]
    {σ : L ≃ₐ[F] L} (hgen : ∀ τ : L ≃ₐ[F] L, τ ∈ Subgroup.zpowers σ)
    (γ : Matrix.GeneralLinearGroup (Fin 2) F) (hγ : γ ∈ AutomorphicForm.hyperbolicCell F)
    (δ : Matrix.GeneralLinearGroup (Fin 2) L)
    (h : LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ δ) = ConjClasses.mk γ) :
    ∃ g : Matrix.GeneralLinearGroup (Fin 2) L,
      ((g⁻¹ * δ * Matrix.GeneralLinearGroup.map (σ : L →+* L) g : Matrix.GeneralLinearGroup (Fin 2) L) :
          Matrix (Fin 2) (Fin 2) L) 1 0 = 0 ∧
      ((g⁻¹ * δ * Matrix.GeneralLinearGroup.map (σ : L →+* L) g : Matrix.GeneralLinearGroup (Fin 2) L) :
          Matrix (Fin 2) (Fin 2) L) 0 1 = 0 := by sorry
