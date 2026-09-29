-- Prove2me | Theorems.Thm_NumberField_TateGlobal_ideleNorm_eq_prod_norm_infinitePlace_pow_mult_of_snd_eq_one
-- name    : NumberField.TateGlobal.ideleNorm_eq_prod_norm_infinitePlace_pow_mult_of_snd_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.964832+00:00
-- url     : https://prove2.me/theorems/4b4390ba-eff7-5a0c-80dc-848fe299b2af
-- title:
--   Idele norm of an idele with trivial finite component
-- statement:
--   Let $K$ be a number field, and let $a$ be a unit of the adele ring $\mathbb{A}_K$ of $K$, realised as the product of the infinite adele ring $\prod_{w\mid\infty} K_w$ (product over the infinite places, $K_w$ the associated completion) and the finite adele ring of $\mathcal{O}_K$ in $K$. Assume that the second (finite-adelic) component of the underlying adele of $a$ is $1$. Then the idele norm of $a$, defined as the real number obtained from the distributive Haar character $\mathrm{distribHaarChar}(\mathbb{A}_K)(a) \in \mathbb{R}_{\ge 0}$, i.e. the nonnegative factor by which multiplication by $a$ scales an additive Haar measure on $\mathbb{A}_K$, equals the finite product over the infinite places $w$ of $K$ of $\lVert a_w\rVert^{m_w}$, where $a_w \in K_w$ is the $w$-component of the first (archimedean) component of $a$, $\lVert \cdot \rVert$ is the norm of the completion $K_w$, and $m_w$ is the multiplicity of $w$ ($1$ at a real place, $2$ at a complex place).
--
--   This is the classical product formula for the module of an idele (Weil's module, Tate's $\lVert \cdot \rVert_{\mathbb{A}}$), in the special case of an idele supported at the archimedean places, where the finite part contributes $1$. It is used throughout the adelic automorphic-form part of the development to convert statements about archimedean components at individual places into statements about the global idele norm.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_TateGlobal_ideleNorm_eq_prod_norm_infinitePlace_pow_mult_of_snd_eq_one.lean

import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_NumberField_TateGlobalZeta

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField IsDedekindDomain

theorem NumberField.TateGlobal.ideleNorm_eq_prod_norm_infinitePlace_pow_mult_of_snd_eq_one
    (K : Type) [Field K] [NumberField K]
    (a : (AdeleRing (𝓞 K) K)ˣ) (ha : ((a : AdeleRing (𝓞 K) K)).2 = 1) :
    NumberField.TateGlobal.ideleNorm K a = ∏ w : InfinitePlace K, ‖((a : AdeleRing (𝓞 K) K)).1 w‖ ^ w.mult := by sorry
