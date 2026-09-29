-- Prove2me | Theorems.Thm_NumberField_distribHaarChar_idelicNorm_genuineBaseChange
-- name    : NumberField.distribHaarChar_idelicNorm_genuineBaseChange
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.964832+00:00
-- url     : https://prove2.me/theorems/367103d6-9b4d-5d0c-b6fe-4ec0bbc98446
-- title:
--   Idelic norm preserves the adelic modulus
-- statement:
--   Let $K$ and $L$ be number fields, with $L$ a finite-dimensional Galois extension of $K$, and let $z$ be a unit of the adele ring $\mathbb{A}_L$ of $L$ (the adele ring of $L$ relative to its ring of integers). The adele base change [`M4aHerbrand.GenuineDescent.genuineBaseChange K L`](def/M4aHerbrand_GenuineDescent.html#L87) packages a ring homomorphism $\beta\colon \mathbb{A}_K \to \mathbb{A}_L$ which on principal adeles is the map induced by $K \hookrightarrow L$, together with an isomorphism of $\mathbb{A}_K$-algebras $\mathbb{A}_K \otimes_K L \cong \mathbb{A}_L$ carrying $1 \otimes l$ to the principal adele of $l$; here $\mathbb{A}_L$ is viewed as an $\mathbb{A}_K$-algebra via $\beta$. Its `idelicNorm` is the homomorphism $\mathbb{A}_L^\times \to \mathbb{A}_K^\times$ obtained by applying `Units.map` to the algebra norm $\mathrm{N}\colon \mathbb{A}_L \to \mathbb{A}_K$ of this $\mathbb{A}_K$-algebra. Writing $\operatorname{distribHaarChar}$ for the factor by which multiplication by a unit scales an additive Haar measure on the ambient ring, the assertion is the equality $$\operatorname{distribHaarChar}_{\mathbb{A}_K}\big(\mathrm{N}(z)\big) = \operatorname{distribHaarChar}_{\mathbb{A}_L}(z)$$ of these two scaling factors, for every such $z$.
--
--   This is the compatibility of the idelic module (the idelic absolute value) with the norm of a finite extension, $|\mathrm{N}_{L/K}z|_{\mathbb{A}_K} = |z|_{\mathbb{A}_L}$, stated here for Galois extensions; it is the global form of the local identity $|\mathrm{N}_{L_w/K_v}x|_v = |x|_w$. It is used in the measure-theoretic estimates for adelic automorphic forms, in particular in the computations of Haar measures of fundamental domains and of (twisted) orbital integrals that invoke the idelic norm of a determinant.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_distribHaarChar_idelicNorm_genuineBaseChange.lean

import Definitions.Def_M4aHerbrand_GenuineDescent

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField

theorem NumberField.distribHaarChar_idelicNorm_genuineBaseChange
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] (z : (AdeleRing (𝓞 L) L)ˣ) :
    MeasureTheory.distribHaarChar (AdeleRing (𝓞 K) K)
        ((M4aHerbrand.GenuineDescent.genuineBaseChange K L).idelicNorm z) =
      MeasureTheory.distribHaarChar (AdeleRing (𝓞 L) L) z := by sorry
