-- Prove2me | Theorems.Thm_M4aHerbrand_IdeleGaloisDescent_measurePreserving_unitsAct
-- name    : M4aHerbrand.IdeleGaloisDescent.measurePreserving_unitsAct
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:11.33382+00:00
-- url     : https://prove2.me/theorems/2e54ee62-65a3-5299-b2a7-14c66ca2d1e3
-- title:
--   Galois action on ideles preserves Haar measure
-- statement:
--   Let $K \subseteq L$ be fields with $L$ a number field and $L/K$ a finite extension, and let $D$ be an idele Galois descent datum for $(\mathcal{O}_L, K, L)$, that is: a monoid homomorphism $\mathrm{act}$ from the group $L \simeq_{\mathrm{alg}[K]} L$ of $K$-algebra automorphisms of $L$ to the group of ring automorphisms of the adele ring $\mathbb{A}_L =$ `AdeleRing (𝓞 L) L`, such that for every $g$ and every $x \in L$ one has $\mathrm{act}(g)(\iota(x)) = \iota(g x)$ for the structure map $\iota : L \to \mathbb{A}_L$, and such that each $\mathrm{act}(g)$ is continuous. Fix $\sigma \in L \simeq_{\mathrm{alg}[K]} L$, equip the unit group $\mathbb{A}_L^{\times}$ with a measurable structure that is the Borel structure of its topology, and let $\nu$ be a Haar measure on $\mathbb{A}_L^{\times}$. Then the multiplicative automorphism of $\mathbb{A}_L^{\times}$ obtained by restricting the ring automorphism $\mathrm{act}(\sigma)$ to units — the value at $\sigma$ of the homomorphism `D.unitsAct` — is measure preserving for $\nu$ on both sides: it is measurable and pushes $\nu$ forward to $\nu$.
--
--   The statement says that the Galois action on the idele group has modulus $1$, so that no Jacobian factor appears when a $\sigma$-twisted integral over $\mathbb{A}_L^{\times}$ is untwisted by substituting $z \mapsto \sigma^{-1} z$. It is used in the identity comparing a twisted orbital integral over the idele class quotient with an integral over the kernel of the idelic norm.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_M4aHerbrand_IdeleGaloisDescent_measurePreserving_unitsAct.lean

import Definitions.Def_M4aHerbrand_IdeleClassVocab

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField

theorem M4aHerbrand.IdeleGaloisDescent.measurePreserving_unitsAct
    (K L : Type) [Field K] [Field L] [NumberField L] [Algebra K L] [FiniteDimensional K L]
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    [MeasurableSpace (AdeleRing (𝓞 L) L)ˣ] [BorelSpace (AdeleRing (𝓞 L) L)ˣ]
    (ν : Measure (AdeleRing (𝓞 L) L)ˣ) [ν.IsHaarMeasure] :
    MeasurePreserving (D.unitsAct σ) ν ν := by sorry
