-- Prove2me | Theorems.Thm_LanglandsTunnell_P2_Artin_resHom_artinFrob_eq_artinFrob_pow_inertiaDeg
-- name    : LanglandsTunnell.P2.Artin.resHom_artinFrob_eq_artinFrob_pow_inertiaDeg
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.012626+00:00
-- url     : https://prove2.me/theorems/fdc165c4-a88d-5f33-81de-036b0af2652f
-- title:
--   Functoriality of Artin Frobenius elements in a tower
-- statement:
--   Let $K$, $M$, $E$, $N$ be number fields with $K$-algebra structures on $M$, $E$, $N$ and with $N$ an $M$-algebra and an $E$-algebra compatibly (the scalar towers $K \subseteq M \subseteq N$ and $K \subseteq E \subseteq N$), assume $M/K$ and $N/E$ Galois, and assume the group $M \simeq_{\mathrm{alg}[K]} M$ of $K$-automorphisms of $M$ is commutative. Let $v$ be a height-one prime of $\mathcal{O}_K$ and $w$ a height-one prime of $\mathcal{O}_E$ whose contraction to $\mathcal{O}_K$ is $v$, and assume that every maximal ideal $Q$ of $\mathcal{O}_M$ contracting to $v$ has trivial inertia subgroup in $\mathrm{Gal}(M/K)$. Write $\mathtt{artinFrob}\,K\,M\,v$ for the arithmetic Frobenius `arithFrobAt` of the $\mathrm{Gal}(M/K)$-action at the chosen prime `primeAbove K M v` of $\mathcal{O}_M$ over $v$, and likewise $\mathtt{artinFrob}\,E\,N\,w$ in $\mathrm{Gal}(N/E)$. Then the image of $\mathtt{artinFrob}\,E\,N\,w$ under `resHom`, the homomorphism $\mathrm{Gal}(N/E) \to \mathrm{Gal}(M/K)$ given by restricting scalars to $K$ and then restricting the resulting automorphism of $N$ to the normal subextension $M$, equals $\mathtt{artinFrob}\,K\,M\,v$ raised to the power $\mathtt{inertiaDeg'}$ of $w$ over $v$, i.e. the residue degree $[\kappa(w):\kappa(v)]$.
--
--   This is the standard functoriality of Frobenius elements in a square of extensions: restricting a $w$-Frobenius of $N/E$ to an abelian subextension $M/K$ unramified above $v$ yields the $f(w\mid v)$-th power of the Frobenius at $v$. It is used in the construction of the Artin map on Hecke characters, where it feeds the comparison of a finite product of Frobenius powers with a product of local contributions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_P2_Artin_resHom_artinFrob_eq_artinFrob_pow_inertiaDeg.lean

import Definitions.Def_LanglandsTunnell_ArtinCoreCTM

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField IsDedekindDomain LanglandsTunnell.P2.Artin

theorem LanglandsTunnell.P2.Artin.resHom_artinFrob_eq_artinFrob_pow_inertiaDeg
    (K M E N : Type*) [Field K] [NumberField K] [Field M] [NumberField M] [Field E] [NumberField E]
    [Field N] [NumberField N]
    [Algebra K M] [Algebra K E] [Algebra K N] [Algebra M N] [Algebra E N]
    [IsScalarTower K M N] [IsScalarTower K E N] [IsGalois K M] [IsGalois E N]
    [IsMulCommutative (M ≃ₐ[K] M)]
    (v : HeightOneSpectrum (𝓞 K)) (w : HeightOneSpectrum (𝓞 E))
    (hwv : w.asIdeal.under (𝓞 K) = v.asIdeal)
    (hunr : ∀ Q : Ideal (𝓞 M), Q.IsMaximal → Q.under (𝓞 K) = v.asIdeal → Q.inertia (M ≃ₐ[K] M) = ⊥) :
    resHom K M E N (artinFrob E N w) = artinFrob K M v ^ v.asIdeal.inertiaDeg' w.asIdeal := by sorry
