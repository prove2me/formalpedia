-- Prove2me | Theorems.Thm_HeightOneSpectrum_adicCompletion_baseChangeAlgEquiv_congr_apply_eq_transport
-- name    : HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv_congr_apply_eq_transport
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.342414+00:00
-- url     : https://prove2.me/theorems/56a1183e-1a40-5e60-ae29-7d3a74494794
-- title:
--   Galois equivariance of the base-change decomposition L⊗_K Kᵥ≅prod_{w∣ v}L_w
-- statement:
--   Let $K$ and $L$ be number fields with $L$ an extension of $K$, let $v$ be a nonzero prime of the ring of integers $\mathcal{O}_K$ (a point of its height one spectrum), and let $\sigma$ be an automorphism of $L$ fixing $K$. Let $w$ and $w'$ be elements of `v.Extension (𝓞 L)`, that is, primes of $\mathcal{O}_L$ whose contraction to $\mathcal{O}_K$ is $v$, and assume $\sigma\cdot w=w'$ for the action of $\sigma$ on primes of $\mathcal{O}_L$. Then for every $y$ in $L\otimes_K K_v$, where $K_v$ is the $v$-adic completion of $K$, the $w'$-component of the image of $(\sigma\otimes\mathrm{id}_{K_v})(y)$ under the $L$-algebra isomorphism `HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv`, $L\otimes_K K_v\xrightarrow{\ \sim\ }\prod_{w''\mid v}L_{w''}$ (the bijective base change of the product of the semialgebra maps to the completions), equals the image of the $w$-component of the image of $y$ under the same isomorphism by [`NumberField.PlaceTransport.transport σ h`](def/NumberField_PlaceTransport.html#L105), the ring isomorphism $L_w\xrightarrow{\ \sim\ }L_{w'}$ obtained by completing the isomorphism of valued fields induced by $\sigma$.
--
--   This is the statement that the canonical decomposition $L\otimes_K K_v\cong\prod_{w\mid v}L_w$ is equivariant for the action of $\mathrm{Gal}(L/K)$, which permutes the primes above $v$ and carries $L_w$ isomorphically to $L_{\sigma w}$; in particular it gives $|((\sigma\otimes 1)y)_{w'}|_{w'}=|y_w|_w$. It is used in later computations with local components of adelic objects, in the treatment of unit groups and of compactness properties of twisted Bruhat data.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HeightOneSpectrum_adicCompletion_baseChangeAlgEquiv_congr_apply_eq_transport.lean

import Definitions.Def_TwistedUnipotentTerm_SemiLocalOrbitalVocab
import Definitions.Def_NumberField_PlaceTransport

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped TensorProduct NumberField.PlaceTransport

theorem HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv_congr_apply_eq_transport
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) (σ : L ≃ₐ[K] L) (w w' : v.Extension (𝓞 L)) (h : σ • w.1 = w'.1)
    (y : L ⊗[K] v.adicCompletion K) :
    HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L (𝓞 L) v
        (Algebra.TensorProduct.congr σ (AlgEquiv.refl : v.adicCompletion K ≃ₐ[K] v.adicCompletion K) y) w' =
      NumberField.PlaceTransport.transport σ h
        (HeightOneSpectrum.adicCompletion.baseChangeAlgEquiv K L (𝓞 L) v y w) := by sorry
