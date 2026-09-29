-- Prove2me | Theorems.Thm_ModularCurve_UnramifiedOutside_of_specializationExists
-- name    : ModularCurve.UnramifiedOutside.of_specializationExists
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.68297+00:00
-- url     : https://prove2.me/theorems/3e95a279-6e77-55d7-8e84-890e93b06ad5
-- title:
--   Inertia acts trivially on p-power torsion outside Np
-- statement:
--   Let $K \subseteq L$ be fields, let $N$ and $p$ be natural numbers, and let $J$ be an additive commutative group carrying a module structure over the abstract Hecke algebra [`ModularCurve.HeckeAlg`](def/HeckeGalois_EichlerShimura.html#L14) $= \mathbb{Z}[X_q : q \text{ prime}]$ (a polynomial ring on the primes) together with a distributive action of the automorphism group $L \simeq_K L$ that commutes with the Hecke action. Assume [`ModularCurve.SpecializationExists`](def/HeckeGalois_EichlerShimura.html#L219) for the data $(N,p,J)$: for every prime $\ell$ with $\ell \nmid Np$ and every valuation subring $A$ of $L$ with $\ell$ a nonunit of $A$, there are an additive commutative group $J'$ with a Hecke-module structure, additive maps $\mathrm{sp} : J \to J'$ and $F : J' \to J'$ such that $\mathrm{sp}$ is Hecke-equivariant, satisfies $\mathrm{sp}(\sigma \cdot x) = \mathrm{sp}(x)$ for $\sigma$ in the image in $L \simeq_K L$ of the inertia subgroup of $A$ over $K$, satisfies $\mathrm{sp}(\sigma \cdot x) = F(\mathrm{sp}(x))$ for every $\sigma$ that is a Frobenius at $\ell$ for $A$, and is injective on $p$-power torsion, and such that $F$ obeys $F^2 y - T_\ell \cdot F y + \ell y = 0$ for all $y \in J'$, where $T_\ell$ is the Hecke generator at $\ell$. Then [`ModularCurve.UnramifiedOutside`](def/HeckeGalois_EichlerShimura.html#L125) holds: for every prime $\ell \nmid Np$, every valuation subring $A$ of $L$ in which $\ell$ is a nonunit, every $\sigma$ in the image of the inertia subgroup of $A$ over $K$, and every $x \in J$ killed by some power of $p$, one has $\sigma \cdot x = x$.
--
--   This is the Néron–Ogg–Shafarevich criterion in packaged form: existence of a specialisation to a special fibre on which inertia acts trivially and which is injective on $p$-power torsion forces the $p$-power torsion of $J$ to be unramified outside $Np$. It supplies the unramifiedness clause of the Eichler–Shimura package for the Galois action on the torsion of the Jacobian, and is used in the verification that the $p$-power torsion attached to the modular curve of interest is unramified outside $Np$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_UnramifiedOutside_of_specializationExists.lean

import Definitions.Def_HeckeGalois_EichlerShimura

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularCurve.UnramifiedOutside.of_specializationExists {K L : Type*} [Field K] [Field L] [Algebra K L] (N p : ℕ) (J : Type*) [AddCommGroup J] [Module ModularCurve.HeckeAlg J] [DistribMulAction (L ≃ₐ[K] L) J] [SMulCommClass (L ≃ₐ[K] L) ModularCurve.HeckeAlg J] (h : ModularCurve.SpecializationExists (K := K) (L := L) N p J) : ModularCurve.UnramifiedOutside (K := K) (L := L) N p J := by sorry
