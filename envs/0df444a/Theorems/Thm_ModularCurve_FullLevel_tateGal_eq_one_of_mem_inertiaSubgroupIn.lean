-- Prove2me | Theorems.Thm_ModularCurve_FullLevel_tateGal_eq_one_of_mem_inertiaSubgroupIn
-- name    : ModularCurve.FullLevel.tateGal_eq_one_of_mem_inertiaSubgroupIn
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:39.1924+00:00
-- url     : https://prove2.me/theorems/84a61468-be5d-5f9a-b343-681a5894e317
-- title:
--   Inertia at ℓ ∤ qM'λ acts trivially on T_λ(Jac)
-- statement:
--   Let $q$ be a prime, $M'$ a nonzero natural number and $\lambda$ a prime, and let $\ell$ be a natural number which is prime, distinct from $q$, not dividing $M'$, and distinct from $\lambda$. Write $\mathrm{Gal}$ for the group of $\mathbb{Q}$-algebra automorphisms of $\mathrm{AlgebraicClosure}\ \mathbb{Q}$. The assertion is that for every valuation subring $P$ of $\mathrm{AlgebraicClosure}\ \mathbb{Q}$ lying over $\ell$ in the sense of `LiesOverPrime`, i.e. such that the image of $\ell$ is a nonunit of $P$, and for every $\sigma$ belonging to `P.inertiaSubgroupIn ℚ`, the image in $\mathrm{Gal}$ of the inertia subgroup of $P$ under the inclusion of its decomposition subgroup, one has $\mathrm{tateGal}\ q\ M'\ \lambda\ \sigma = 1$. Here `tateGal` is the composite of the Galois action `galJac` on the group `Jac q M'`, given by sending $x$ to the element whose $\zeta$-component is $\sigma \cdot x.\mathrm{eval}(\sigma^{-1} \cdot \zeta)$, with the functorial map `tateEnd` from additive endomorphisms of `Jac q M'` to $\mathbb{Z}_\lambda$-linear endomorphisms of [`TateModule lam (Jac q M')`](def/EllipticCurve_TateModule.html#L15), the group of sequences $(x_n)$ in `Jac q M'` with $\lambda^n x_n = 0$ and $\lambda x_{n+1} = x_n$. Thus $\sigma$ acts as the identity on this $\lambda$-adic Tate module.
--
--   This is the Néron–Ogg–Shafarevich criterion, in the form 'good reduction implies unramified', for the Jacobian attached to the modular curve of full level $q$ with $\Gamma_0(M')$-structure away from $q$: the $\lambda$-adic Tate module is unramified at every prime $\ell$ prime to $qM'\lambda$. It supplies the unramifiedness condition in the construction of the full-level Tate datum, and is used by the two existence theorems for such data producing eigen-isomorphisms and Drinfeld specialisations.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_FullLevel_tateGal_eq_one_of_mem_inertiaSubgroupIn.lean

import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_GaloisRep_Adic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve ModularCurve.FullLevel

theorem ModularCurve.FullLevel.tateGal_eq_one_of_mem_inertiaSubgroupIn
    (q : ℕ) [Fact q.Prime] (M' : ℕ) [NeZero M'] (lam : ℕ) [Fact lam.Prime]
    (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓq : ℓ ≠ q) (hℓM' : ¬ ℓ ∣ M') (hℓlam : ℓ ≠ lam) :
    ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime ℓ →
      ∀ σ ∈ P.inertiaSubgroupIn ℚ, tateGal q M' lam σ = 1 := by sorry
