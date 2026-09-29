-- Prove2me | Theorems.Thm_NumberField_InfiniteAdeleRing_exists_continuousMulEquiv_units_pi_forall_apply_eq_archFibre
-- name    : NumberField.InfiniteAdeleRing.exists_continuousMulEquiv_units_pi_forall_apply_eq_archFibre
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.923973+00:00
-- url     : https://prove2.me/theorems/37665aca-d988-52fb-8a21-8e7841684eb2
-- title:
--   Regrouping the infinite adelic unit group over places of K
-- statement:
--   Let $K$ and $L$ be number fields (fields of characteristic zero with the `NumberField` property) and let $L$ be a $K$-algebra. For an infinite place $v$ of $K$, write $v.\mathrm{Extension}\,L$ for the subtype of infinite places $w$ of $L$ with $w \circ \mathrm{algebraMap}\,K\,L = v$ (the places of $L$ above $v$). The assertion is that there exists a continuous multiplicative isomorphism, i.e. an isomorphism of topological groups,
--   $$E : (\mathrm{InfiniteAdeleRing}\,L)^{\times} \;\simeq\; \prod_{v}\Bigl(\prod_{w \mid v} L_w\Bigr)^{\times},$$
--   the outer product being over all infinite places $v$ of $K$ and the inner product over $w : v.\mathrm{Extension}\,L$ of the completions $w.1.\mathrm{Completion}$, such that for every unit $y$ of the infinite adele ring of $L$ and every infinite place $v$ of $K$ the $v$-component of $E y$ equals $\mathrm{archFibre}\,K\,L\,v\,y$; here $\mathrm{archFibre}\,K\,L\,v$ is the monoid homomorphism on unit groups induced by the ring homomorphism $\mathrm{InfiniteAdeleRing}\,L = \prod_{u : \mathrm{InfinitePlace}\,L} u.\mathrm{Completion} \to \prod_{w \mid v} w.1.\mathrm{Completion}$ whose components are the coordinate projections at the places above $v$. The statement is existential: no particular isomorphism is named, only one whose components are the fibre maps.
--
--   This records the classical decomposition $L_\infty^{\times} \cong \prod_{v \mid \infty}(L \otimes_K K_v)^{\times}$ of the archimedean idele group of $L$ according to the places of $K$ below those of $L$, in the form needed to treat the archimedean part of an idele of $L$ as a single variable indexed by places of $K$. It is used by the measure-theoretic statements about the transversal measure and the twisted Bruhat decomposition, where integration over the archimedean component is performed place by place over $K$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_InfiniteAdeleRing_exists_continuousMulEquiv_units_pi_forall_apply_eq_archFibre.lean

import Definitions.Def_AutomorphicForm_TransversalMeasure

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField

theorem NumberField.InfiniteAdeleRing.exists_continuousMulEquiv_units_pi_forall_apply_eq_archFibre
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] :
    ∃ E : (InfiniteAdeleRing L)ˣ ≃ₜ* (∀ v : InfinitePlace K, (∀ w : v.Extension L, w.1.Completion)ˣ),
      ∀ (y : (InfiniteAdeleRing L)ˣ) (v : InfinitePlace K),
        E y v = AutomorphicForm.TransversalMeasure.archFibre K L v y := by sorry
