-- Prove2me | Theorems.Thm_M4aHerbrand_IdeleGaloisDescent_ideleNorm_unitsAct
-- name    : M4aHerbrand.IdeleGaloisDescent.ideleNorm_unitsAct
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.33382+00:00
-- url     : https://prove2.me/theorems/0e53eeea-65f0-533c-a742-985fcb091415
-- title:
--   Galois invariance of the idele norm
-- statement:
--   Let $K$ and $L$ be fields with $L$ a number field and $L$ a $K$-algebra, and let $D$ be an idele Galois descent datum for $\mathcal{O}_L$, $K$, $L$: that is, a monoid homomorphism $D.\mathrm{act}$ from the group $L \simeq_{\mathrm{alg}[K]} L$ of $K$-algebra automorphisms of $L$ to the group of ring automorphisms of the adele ring $\mathbb{A}_L =$ `AdeleRing (𝓞 L) L`, such that $D.\mathrm{act}(g)$ restricted along the structure map $L \to \mathbb{A}_L$ agrees with $g$ for every $g$ and every $x \in L$, and such that each $D.\mathrm{act}(g)$ is continuous. Let $\sigma$ be a $K$-algebra automorphism of $L$ and let $z$ be a unit of $\mathbb{A}_L$. Then the idele norm of $(D.\mathrm{unitsAct}\,\sigma)(z)$ equals that of $z$, where $D.\mathrm{unitsAct}\,\sigma$ is the multiplicative automorphism of $\mathbb{A}_L^{\times}$ obtained by applying $D.\mathrm{act}\,\sigma$ to units, and where [`NumberField.TateGlobal.ideleNorm L`](def/NumberField_TateGlobalZeta.html#L19) sends a unit $x$ to the real number underlying the nonnegative real value at $x$ of the distributive Haar character `distribHaarChar` of $\mathbb{A}_L$.
--
--   This is the statement that the idelic modulus $\|\cdot\|_{\mathbb{A}_L}$, defined here as the scaling factor of additive Haar measure under multiplication, is invariant under a Galois action on the adeles; classically it reflects the place-by-place identity $|\sigma z|_{\sigma w} = |z|_w$. It is used in the analytic estimates for twisted orbital integrals of automorphic forms, where invariance of the modulus under the Galois action is needed.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_M4aHerbrand_IdeleGaloisDescent_ideleNorm_unitsAct.lean

import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_M4aHerbrand_IdeleClassVocab

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField

theorem M4aHerbrand.IdeleGaloisDescent.ideleNorm_unitsAct
    (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L]
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L) (z : (AdeleRing (𝓞 L) L)ˣ) :
    NumberField.TateGlobal.ideleNorm L (D.unitsAct σ z) = NumberField.TateGlobal.ideleNorm L z := by sorry
