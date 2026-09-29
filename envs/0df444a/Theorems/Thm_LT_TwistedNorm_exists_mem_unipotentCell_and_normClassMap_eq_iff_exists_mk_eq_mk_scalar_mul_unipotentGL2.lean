-- Prove2me | Theorems.Thm_LT_TwistedNorm_exists_mem_unipotentCell_and_normClassMap_eq_iff_exists_mk_eq_mk_scalar_mul_unipotentGL2
-- name    : LT.TwistedNorm.exists_mem_unipotentCell_and_normClassMap_eq_iff_exists_mk_eq_mk_scalar_mul_unipotentGL2
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:00.858323+00:00
-- url     : https://prove2.me/theorems/495dc79b-4f5b-5bab-bf4e-7640e337222a
-- title:
--   Unipotent norm class iff σ-conjugate to ζ n(b), Tr(b)≠ 0
-- statement:
--   Let $F \subseteq L$ be fields with $L$ a finite-dimensional Galois extension of $F$, let $\sigma$ be an $F$-algebra automorphism of $L$ such that every $F$-algebra automorphism $\tau$ of $L$ lies in the subgroup of integer powers of $\sigma$ (so $\sigma$ generates the Galois group), and let $\delta \in GL_2(L)$. Write $[\delta]_\sigma$ for [`LT.TwistedNorm.SigmaConjClasses.mk σ δ`](def/TwistedNormClasses.html#L718), the class of $\delta$ in the quotient of $GL_2(L)$ by $\sigma$-conjugacy, the relation [`AutomorphicForm.IsSigmaConj`](def/AutomorphicForm_SigmaConjugacy.html#L15) which holds between $\delta_1$ and $\delta_2$ exactly when $\delta_2 = k^{-1}\delta_1\,\sigma(k)$ for some $k \in GL_2(L)$; and let `normClassMap hgen` be the map to $GL_2(F)$-conjugacy classes sending $[\delta]_\sigma$ to the conjugacy class of a norm representative `normRep hgen δ` $\in GL_2(F)$ of $\delta$, chosen by `exists_map_eq_conj_sigmaNormPow` and independent of the representative of the $\sigma$-class. The theorem asserts the equivalence of: (i) there is $\gamma \in GL_2(F)$ lying in [`AutomorphicForm.unipotentCell F`](def/AutomorphicForm_GL2ConjugacyCells.html#L29), that is, the underlying matrix of $\gamma$ does not satisfy `IsCentralType` and its characteristic polynomial is $(X - C\,a)^2$ for some $a \in F$, with `normClassMap hgen` $[\delta]_\sigma$ equal to the conjugacy class of $\gamma$; and (ii) there are $\zeta \in L^\times$ and $b \in L$ with $\mathrm{Tr}_{L/F}(b) \neq 0$ and $[\delta]_\sigma = [\,\zeta \cdot n(b)\,]_\sigma$, where $\zeta \cdot n(b)$ is the scalar matrix $\zeta$ times [`AutomorphicForm.unipotentGL2 b = !![1, b; 0, 1]`](def/AutomorphicForm_ConstantTerm.html#L17).
--
--   This is the classification of the $\sigma$-conjugacy classes in $GL_2(L)$ whose norm class is of unipotent type, for a cyclic Galois extension $L/F$: such classes are exactly those containing a scalar multiple of a unipotent matrix $n(b)$ with $\mathrm{Tr}_{L/F}(b) \neq 0$. It serves the indexing of the unipotent-type contributions on the geometric side of the twisted trace formula for $GL_2$, and is used by the companion result [`LT.TwistedNorm.exists_mem_unipotentCell_and_normClassMap_eq_iff_exists_mul_eq_mul_map_and_trace_ne_zero_of_apply_one_zero_eq_zero`](thm.html#LT.TwistedNorm.exists_mem_unipotentCell_and_normClassMap_eq_iff_exists_mul_eq_mul_map_and_trace_ne_zero_of_apply_one_zero_eq_zero), which recasts the criterion in terms of an explicit matrix identity.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LT_TwistedNorm_exists_mem_unipotentCell_and_normClassMap_eq_iff_exists_mk_eq_mk_scalar_mul_unipotentGL2.lean

import Definitions.Def_TwistedNormClasses
import Definitions.Def_AutomorphicForm_GL2ConjugacyCells
import Definitions.Def_AutomorphicForm_ConstantTerm

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem LT.TwistedNorm.exists_mem_unipotentCell_and_normClassMap_eq_iff_exists_mk_eq_mk_scalar_mul_unipotentGL2
    {F L : Type*} [Field F] [Field L] [Algebra F L] [FiniteDimensional F L] [IsGalois F L]
    {σ : L ≃ₐ[F] L} (hgen : ∀ τ : L ≃ₐ[F] L, τ ∈ Subgroup.zpowers σ)
    (δ : Matrix.GeneralLinearGroup (Fin 2) L) :
    (∃ γ : Matrix.GeneralLinearGroup (Fin 2) F, γ ∈ AutomorphicForm.unipotentCell F ∧
        LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ δ) = ConjClasses.mk γ) ↔
      ∃ (ζ : Lˣ) (b : L), Algebra.trace F L b ≠ 0 ∧
        LT.TwistedNorm.SigmaConjClasses.mk σ δ =
          LT.TwistedNorm.SigmaConjClasses.mk σ
            (Matrix.GeneralLinearGroup.scalar (Fin 2) ζ * AutomorphicForm.unipotentGL2 b) := by sorry
