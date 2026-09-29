-- Prove2me | Theorems.Thm_NumberField_TateGlobal_ideleNorm_idelesBaseChange
-- name    : NumberField.TateGlobal.ideleNorm_idelesBaseChange
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.964832+00:00
-- url     : https://prove2.me/theorems/3d35f501-b172-5282-81b9-bc6e806a0e4c
-- title:
--   Idelic norm of a base-changed idele
-- statement:
--   Let $K$ and $L$ be number fields with $L$ an algebra over $K$, finite-dimensional over $K$ and Galois over $K$, and let $y$ be a unit of the adele ring $\mathbb{A}_K$ of $K$ (the adele ring of $K$ relative to its ring of integers $\mathcal{O}_K$). Write $\|x\|_F$ for [`NumberField.TateGlobal.ideleNorm F x`](def/NumberField_TateGlobalZeta.html#L19), the real number obtained by coercing the value at $x$ of the distributive Haar character `distribHaarChar` of the additive group $\mathbb{A}_F$, taken with respect to the scaling action of the ideles $\mathbb{A}_F^{\times}$; and let [`AutomorphicForm.TransversalMeasure.idelesBaseChange K L`](def/AutomorphicForm_TransversalMeasure.html#L85) be the monoid homomorphism $\mathbb{A}_K^{\times} \to \mathbb{A}_L^{\times}$ obtained by applying `Units.map` to the multiplicative map underlying the ring homomorphism $\beta =$ [`M4aHerbrand.Bridge.genuineβ K L`](def/M4aHerbrand_GenuineBeta.html#L14) $: \mathbb{A}_K \to \mathbb{A}_L$. The assertion is the equality of real numbers
--   $$\|\,\beta(y)\,\|_{L} \;=\; \|y\|_{K}^{\,\operatorname{finrank}_K L},$$
--   where $\operatorname{finrank}_K L = [L:K]$ is the $K$-dimension of $L$.
--
--   This is the statement that the idelic modulus is multiplicative of exponent $[L:K]$ along a base change of ideles, equivalently that $\prod_{w \mid v} \|y_v\|_w = \|y_v\|_v^{[L:K]}$ place by place. It is used to convert norm levels and height cut-offs on the ideles of $L$ into ones on the ideles of $K$ in the transversal decomposition arguments for twisted unipotent terms, and in the identification of principal ranges as fixed points of the unit base-change map.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_TateGlobal_ideleNorm_idelesBaseChange.lean

import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_AutomorphicForm_TransversalMeasure
import Definitions.Def_M4aHerbrand_GenuineDescent

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField

theorem NumberField.TateGlobal.ideleNorm_idelesBaseChange
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] (y : (AdeleRing (𝓞 K) K)ˣ) :
    NumberField.TateGlobal.ideleNorm L (AutomorphicForm.TransversalMeasure.idelesBaseChange K L y) =
      NumberField.TateGlobal.ideleNorm K y ^ Module.finrank K L := by sorry
