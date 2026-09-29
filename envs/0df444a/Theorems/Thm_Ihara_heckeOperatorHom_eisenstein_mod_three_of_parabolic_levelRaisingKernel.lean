-- Prove2me | Theorems.Thm_Ihara_heckeOperatorHom_eisenstein_mod_three_of_parabolic_levelRaisingKernel
-- name    : Ihara.heckeOperatorHom_eisenstein_mod_three_of_parabolic_levelRaisingKernel
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.515241+00:00
-- url     : https://prove2.me/theorems/27f366e0-dd6d-5083-8581-ca0696b91b69
-- title:
--   Mod-3 kernel pairs for Γ₀(Nq) are Eisenstein
-- statement:
--   Let $N$ and $q$ be natural numbers with $q$ prime and $q \nmid N$, and let $\varphi, \psi \colon \mathrm{Hom}(\Gamma_0(N), \mathbb{Z})$ be additive homomorphisms from $\mathrm{Additive}\,\Gamma_0(N)$ to $\mathbb{Z}$ which are parabolic in the sense of [`ModularCurve.Period.parabolicHoms`](def/ModularCurve_PeriodMap.html#L62), i.e. each vanishes on every $\gamma \in \Gamma_0(N)$ whose matrix satisfies $(\operatorname{tr}\gamma)^2 = 4$. Assume the pair $(\varphi,\psi)$ lies in the kernel modulo $3$ of the two maps [`Ihara.ι₀ N q`](def/IharaIota.html#L17) and [`Ihara.ι₁ N q`](def/IharaIota.html#L111) from $\Gamma_0(Nq)$ into $\mathrm{Additive}\,\Gamma_0(N)$, that is, $3 \mid \varphi(\iota_0(\gamma)) + \psi(\iota_1(\gamma))$ in $\mathbb{Z}$ for every $\gamma \in \Gamma_0(Nq)$. Let $\ell$ be a nonzero prime with $\ell \nmid Nq$, and let $T_\ell =$ [`HeckeEis.heckeOperatorHom N ℓ ℤ`](def/Gamma0HeckeOperatorHom.html#L285) be the endomorphism of $\mathrm{Hom}(\mathrm{Additive}\,\Gamma_0(N), \mathbb{Z})$ obtained by pulling back along the homomorphism `Ihara.heckeConj N ℓ` from the finite-index subgroup $\mathrm{heckeUpper}(N,\ell) = (\mathrm{heckeUpperSL}\,\ell)\cap\Gamma_0(N)$ to $\Gamma_0(N)$ and then applying the transfer (corestriction) back to $\Gamma_0(N)$, summing over the cosets of $\mathrm{heckeUpper}(N,\ell)$. Then there exist homomorphisms $\varphi', \psi' \colon \mathrm{Additive}\,\Gamma_0(N) \to \mathbb{Z}$ with $T_\ell\varphi - (\ell+1)\varphi = 3\varphi'$ and $T_\ell\psi - (\ell+1)\psi = 3\psi'$; the auxiliary homomorphisms $\varphi'$, $\psi'$ are not required to be parabolic.
--
--   This is the mod-3 form of Ribet's description of the kernel of the degeneracy map $J_0(N)^2 \to J_0(Nq)$, transported to integral parabolic classes: a pair of parabolic homomorphisms annihilating that kernel modulo $3$ is Eisenstein modulo $3$ for every Hecke operator at a prime $\ell \nmid Nq$. It is used in the level-raising analysis, in [`LevelRaising.qNewSupport_comap_of_isNormalizedEigenform_oddPrime`](thm.html#LevelRaising.qNewSupport_comap_of_isNormalizedEigenform_oddPrime), to exclude Eisenstein behaviour when comparing $q$-new supports of normalised eigenforms.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Ihara_heckeOperatorHom_eisenstein_mod_three_of_parabolic_levelRaisingKernel.lean

import Definitions.Def_IharaIota
import Definitions.Def_Gamma0HeckeOperatorHom
import Definitions.Def_ModularCurve_PeriodMap

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem Ihara.heckeOperatorHom_eisenstein_mod_three_of_parabolic_levelRaisingKernel
    (N q : ℕ) (hq : q.Prime) (hqN : ¬ q ∣ N)
    (φ ψ : Additive (CongruenceSubgroup.Gamma0 N) →+ ℤ)
    (hφ : φ ∈ ModularCurve.Period.parabolicHoms ℤ (CongruenceSubgroup.Gamma0 N) ℤ)
    (hψ : ψ ∈ ModularCurve.Period.parabolicHoms ℤ (CongruenceSubgroup.Gamma0 N) ℤ)
    (hker : ∀ γ : CongruenceSubgroup.Gamma0 (N * q),
      (3 : ℤ) ∣ φ (Ihara.ι₀ N q γ) + ψ (Ihara.ι₁ N q γ))
    {ℓ : ℕ} [NeZero ℓ] (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ N * q) :
    (∃ φ' : Additive (CongruenceSubgroup.Gamma0 N) →+ ℤ,
        HeckeEis.heckeOperatorHom N ℓ ℤ φ - ((ℓ : ℤ) + 1) • φ = (3 : ℤ) • φ') ∧
    (∃ ψ' : Additive (CongruenceSubgroup.Gamma0 N) →+ ℤ,
        HeckeEis.heckeOperatorHom N ℓ ℤ ψ - ((ℓ : ℤ) + 1) • ψ = (3 : ℤ) • ψ') := by sorry
