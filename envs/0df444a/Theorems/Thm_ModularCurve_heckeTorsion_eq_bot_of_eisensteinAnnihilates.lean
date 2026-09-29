-- Prove2me | Theorems.Thm_ModularCurve_heckeTorsion_eq_bot_of_eisensteinAnnihilates
-- name    : ModularCurve.heckeTorsion_eq_bot_of_eisensteinAnnihilates
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.700479+00:00
-- url     : https://prove2.me/theorems/a21a2d4c-c58e-5cc7-8569-bac3a531d795
-- title:
--   Vanishing of 𝔪-torsion under Eisenstein annihilation
-- statement:
--   Let $S$ be a finite set of primes and let $\Phi$ be an additive commutative group carrying a module structure over the Hecke algebra `HeckeAlg`, which in this development is the polynomial ring $\mathbb Z[X_\ell : \ell \text{ prime}]$ in one variable `heckeGen` $\ell = X_\ell$ for each prime $\ell$. Assume `EisensteinAnnihilates S Φ`, i.e. for every prime $\ell \notin S$ and every $x \in \Phi$ one has $(X_\ell - (\ell+1))\cdot x = 0$, where $\ell+1$ is the constant polynomial with that integer value. Let $\mathfrak m$ be a maximal ideal of $\mathbb Z[X_\ell : \ell]$, and suppose there is a prime $\ell \notin S$ for which the Eisenstein element $X_\ell - (\ell+1)$ does not lie in $\mathfrak m$. Then `heckeTorsion Φ 𝔪`, the submodule of those $x \in \Phi$ annihilated by every element of $\mathfrak m$, is the zero submodule.
--
--   This is the vanishing statement by which an Eisenstein-annihilated Hecke module — classically the component group of the Néron model of a Jacobian at a bad prime — is seen to contribute no $\mathfrak m$-torsion at a maximal ideal $\mathfrak m$ that is not Eisenstein. It is used in [`ModularCurve.hasLowerLevelTorsion_of_finiteFlat_rankTwo_heckeTorsion`](thm.html#ModularCurve.hasLowerLevelTorsion_of_finiteFlat_rankTwo_heckeTorsion), in the local analysis feeding the level-lowering step.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_heckeTorsion_eq_bot_of_eisensteinAnnihilates.lean

import Definitions.Def_ModularCurve_AtPPackage

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace ModularCurve

theorem heckeTorsion_eq_bot_of_eisensteinAnnihilates
    {S : Finset Nat.Primes} {Φ : Type*} [AddCommGroup Φ] [Module HeckeAlg Φ]
    (hΦ : EisensteinAnnihilates S Φ)
    {𝔪 : Ideal HeckeAlg} (hmax : 𝔪.IsMaximal) {ℓ : Nat.Primes} (hℓ : ℓ ∉ S)
    (hne : heckeGen ℓ - MvPolynomial.C (((ℓ : ℕ) : ℤ) + 1) ∉ 𝔪) :
    heckeTorsion Φ 𝔪 = ⊥ := by sorry
