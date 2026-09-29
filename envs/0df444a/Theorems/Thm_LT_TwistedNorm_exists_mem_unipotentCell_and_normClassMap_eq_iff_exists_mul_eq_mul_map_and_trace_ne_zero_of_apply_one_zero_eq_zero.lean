-- Prove2me | Theorems.Thm_LT_TwistedNorm_exists_mem_unipotentCell_and_normClassMap_eq_iff_exists_mul_eq_mul_map_and_trace_ne_zero_of_apply_one_zero_eq_zero
-- name    : LT.TwistedNorm.exists_mem_unipotentCell_and_normClassMap_eq_iff_exists_mul_eq_mul_map_and_trace_ne_zero_of_apply_one_zero_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:00.858323+00:00
-- url     : https://prove2.me/theorems/270732da-09f0-5d04-9393-32180428ee46
-- title:
--   Unipotent norm class for upper triangular δ
-- statement:
--   Let $F \subseteq L$ be fields with $L$ a finite-dimensional Galois extension of $F$, and let $\sigma$ be an $F$-algebra automorphism of $L$ such that every element of $\mathrm{Gal}(L/F)$ lies in the subgroup of integer powers of $\sigma$ (so the Galois group is cyclic with generator $\sigma$). Let $\delta \in \mathrm{GL}_2(L)$ have lower-left entry $\delta_{10} = 0$, i.e. be upper triangular. The assertion is an equivalence. On the left: there exists $\gamma \in \mathrm{GL}_2(F)$ lying in [`AutomorphicForm.unipotentCell F`](def/AutomorphicForm_GL2ConjugacyCells.html#L29) — that is, the matrix of $\gamma$ is not of central type (the predicate `IsCentralType` fails for it) and its characteristic polynomial equals $(X - a)^2$ for some $a \in F$ — such that the image under [`LT.TwistedNorm.normClassMap hgen`](def/TwistedNormClasses.html#L766) of the $\sigma$-conjugacy class of $\delta$ (the class of $\delta$ modulo the relation $\delta \sim k^{-1}\delta\,\sigma(k)$, sent to the $\mathrm{GL}_2(F)$-conjugacy class of a chosen $F$-rational representative of the $\sigma$-norm string of $\delta$) is the conjugacy class of $\gamma$. On the right: there exists $r \in L$, $r \neq 0$, with $\delta_{00}\, r = \delta_{11}\,\sigma(r)$ and $\mathrm{Tr}_{L/F}\!\left(r\,\delta_{01}/\delta_{11}\right) \neq 0$.
--
--   This is the explicit criterion, for an upper triangular element of $\mathrm{GL}_2$ over a cyclic extension, for its twisted norm class to be of unipotent type: the diagonal ratio must be of the form $\sigma(r)/r$ and an associated trace must be non-zero. It refines the general classification of twisted classes with unipotent norm into a condition on the entries of $\delta$, and is used in the computation of the unipotent and Iwasawa contributions to twisted Bruhat-cell sums and of the corresponding constant-term integrals.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LT_TwistedNorm_exists_mem_unipotentCell_and_normClassMap_eq_iff_exists_mul_eq_mul_map_and_trace_ne_zero_of_apply_one_zero_eq_zero.lean

import Definitions.Def_TwistedNormClasses
import Definitions.Def_AutomorphicForm_GL2ConjugacyCells
import Definitions.Def_AutomorphicForm_ConstantTerm

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem LT.TwistedNorm.exists_mem_unipotentCell_and_normClassMap_eq_iff_exists_mul_eq_mul_map_and_trace_ne_zero_of_apply_one_zero_eq_zero
    {F L : Type*} [Field F] [Field L] [Algebra F L] [FiniteDimensional F L] [IsGalois F L]
    {σ : L ≃ₐ[F] L} (hgen : ∀ τ : L ≃ₐ[F] L, τ ∈ Subgroup.zpowers σ)
    (δ : Matrix.GeneralLinearGroup (Fin 2) L) (hδ : (δ : Matrix (Fin 2) (Fin 2) L) 1 0 = 0) :
    (∃ γ : Matrix.GeneralLinearGroup (Fin 2) F, γ ∈ AutomorphicForm.unipotentCell F ∧
        LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ δ) = ConjClasses.mk γ) ↔
      ∃ r : L, r ≠ 0 ∧
        (δ : Matrix (Fin 2) (Fin 2) L) 0 0 * r = (δ : Matrix (Fin 2) (Fin 2) L) 1 1 * σ r ∧
        Algebra.trace F L (r * (δ : Matrix (Fin 2) (Fin 2) L) 0 1 / (δ : Matrix (Fin 2) (Fin 2) L) 1 1) ≠ 0 := by sorry
