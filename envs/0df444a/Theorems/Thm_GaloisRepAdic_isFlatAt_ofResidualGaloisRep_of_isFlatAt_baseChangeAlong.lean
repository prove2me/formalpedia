-- Prove2me | Theorems.Thm_GaloisRepAdic_isFlatAt_ofResidualGaloisRep_of_isFlatAt_baseChangeAlong
-- name    : GaloisRepAdic.isFlatAt_ofResidualGaloisRep_of_isFlatAt_baseChangeAlong
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:46.235172+00:00
-- url     : https://prove2.me/theorems/a75b44fe-095c-5527-a3d4-4d143cf711f2
-- title:
--   Flatness at p descends along coefficient field extension
-- statement:
--   Let $k_0$ and $k$ be fields, let $\varphi \colon k_0 \to k$ be a ring homomorphism, let $\rho$ be a residual Galois representation over $k_0$ — that is, a $k_0$-vector space $V$ with $\dim_{k_0} V = 2$ together with a monoid homomorphism $\rho \colon \mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q) \to \mathrm{End}_{k_0}(V)$ that is trivial on the subgroup fixing some intermediate field $L$ with $[L:\mathbb Q]$ finite — and let $p$ be a natural number. Both $\rho$ and its scalar extension $\rho \otimes_{k_0} k$ along $\varphi$ (with underlying module $k \otimes_{k_0} V$ and $\sigma$ acting by the base change of $\rho(\sigma)$) are regarded as adic Galois representations over the local rings $k_0$, $k$ via [`GaloisRepAdic.ofResidualGaloisRep`](def/GaloisRep_Adic.html#L196). The hypothesis is `IsFlatAt p` for the base change: the residue field of $k$ is finite, and for every ideal $I$ of $k$ with $k/I$ finite there is a commutative ring $H$ carrying a cocommutative Hopf algebra structure over the subring of $\mathbb Q$ of rationals whose denominator is coprime to $p$, module-finite and flat over that subring, together with a bijection $e$ from $\mathrm{Hom}_{\text{alg}}(H, \overline{\mathbb Q})$ (with its convolution multiplication) onto $(k \otimes_{k_0} V)/(I \cdot \top)$ carrying products to sums and intertwining the Galois action on points with the induced action on the quotient. The conclusion asserts the same property `IsFlatAt p` for $\rho$ itself over $k_0$.
--
--   This is the descent direction of the base-change compatibility of the flat (finite flat group scheme) condition on a residual two-dimensional Galois representation: flatness at $p$ for the representation obtained by enlarging the coefficient field implies flatness at $p$ over the original field. It is used in the construction of patching data for residually modular representations and in relating the failure of flatness at $p$ of the mod $p$ representation of an elliptic curve to the failure of the associated local condition.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GaloisRepAdic_isFlatAt_ofResidualGaloisRep_of_isFlatAt_baseChangeAlong.lean

import Mathlib
import Definitions.Def_GaloisRep_Flat
import Definitions.Def_GaloisRep_Residual

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem GaloisRepAdic.isFlatAt_ofResidualGaloisRep_of_isFlatAt_baseChangeAlong
    {k₀ k : Type} [Field k₀] [Field k] (φ : k₀ →+* k) (ρ : ResidualGaloisRep k₀) (p : ℕ)
    (h : (GaloisRepAdic.ofResidualGaloisRep (ρ.baseChangeAlong φ)).IsFlatAt p) :
    (GaloisRepAdic.ofResidualGaloisRep ρ).IsFlatAt p := by sorry
