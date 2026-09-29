-- Prove2me | Theorems.Thm_GaloisRepAdic_residual_baseChangeAlong_isEquiv
-- name    : GaloisRepAdic.residual_baseChangeAlong_isEquiv
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:47.88569+00:00
-- url     : https://prove2.me/theorems/252fb7b5-7a50-5355-81f7-9368b2cc607d
-- title:
--   Residual representation commutes with coefficient base change
-- statement:
--   Let $A$ and $B$ be commutative local rings, let $\varphi : A \to B$ be a ring homomorphism which is local (it carries non-units to non-units), and let $\rho$ be a [`GaloisRepAdic`](def/GaloisRep_Adic.html#L16) over $A$: a free $A$-module $V$ of finite type with $\operatorname{rank}_A V = 2$, together with a monoid homomorphism from $\operatorname{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$, realised as the $\mathbb{Q}$-algebra automorphisms of `AlgebraicClosure ℚ`, to $\operatorname{End}_A V$, subject to the adic continuity condition that for every $n$ there is a finite-dimensional intermediate field $L$ of $\overline{\mathbb{Q}}/\mathbb{Q}$ such that every $\sigma$ fixing $L$ pointwise satisfies $\rho(\sigma)v - v \in \mathfrak{m}_A^{\,n}\cdot V$ for all $v \in V$. The assertion is that two residual representations over the residue field of $B$ are equivalent: on one side, the base change of $\rho$ along $\varphi$, namely $B \otimes_A V$ with $\sigma$ acting by $1 \otimes \rho(\sigma)$, reduced to $k_B \otimes_B (B \otimes_A V)$; on the other, the reduction $k_A \otimes_A V$ of $\rho$, base changed along the induced residue field map $k_A \to k_B$, namely $k_B \otimes_{k_A} (k_A \otimes_A V)$. Equivalence means: there exists a $k_B$-linear isomorphism between the two underlying spaces intertwining the two Galois actions for every $\sigma$.
--
--   This is the functoriality of passage to the residual representation under a local change of coefficient ring: reducing after base change agrees, up to equivalence of two-dimensional residual representations, with base changing the reduction along the induced map of residue fields. It is used repeatedly in the Taylor–Wiles arguments over Hecke rings, where residual representations attached to eigenforms are compared after transport along algebra maps of local coefficient rings.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GaloisRepAdic_residual_baseChangeAlong_isEquiv.lean

import Definitions.Def_GaloisRep_Adic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped TensorProduct
open Polynomial

theorem GaloisRepAdic.residual_baseChangeAlong_isEquiv
    {A B : Type} [CommRing A] [IsLocalRing A] [CommRing B] [IsLocalRing B]
    (φ : A →+* B) (hφ : IsLocalHom φ) (ρ : GaloisRepAdic A) :
    (ρ.baseChangeAlong φ hφ).residual.IsEquiv
      (ρ.residual.baseChangeAlong (haveI := hφ; IsLocalRing.ResidueField.map φ)) := by sorry
