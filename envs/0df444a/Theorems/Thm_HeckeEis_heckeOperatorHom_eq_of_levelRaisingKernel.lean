-- Prove2me | Theorems.Thm_HeckeEis_heckeOperatorHom_eq_of_levelRaisingKernel
-- name    : HeckeEis.heckeOperatorHom_eq_of_levelRaisingKernel
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.342414+00:00
-- url     : https://prove2.me/theorems/bd4a1f5b-6e89-5847-a3c0-bdc2372ea36f
-- title:
--   Kernel of level raising is Eisenstein for all T_ℓ
-- statement:
--   Let $N$ and $q$ be natural numbers with $q$ prime and $q \nmid N$, and let $A$ be an additive abelian group in which $a+a=0$ implies $a=0$ and $a+a+a=0$ implies $a=0$ (no $2$- and no $3$-torsion). Let $\varphi,\psi \colon \mathrm{Additive}(\Gamma_0(N)) \to A$ be additive homomorphisms, i.e. homomorphisms from $\Gamma_0(N)$ to $A$ written additively, and assume the level-raising kernel condition $\varphi(\iota_0\gamma) + \psi(\iota_1\gamma) = 0$ for every $\gamma \in \Gamma_0(Nq)$, where [`Ihara.ι₀ N q`](def/IharaIota.html#L17) and [`Ihara.ι₁ N q`](def/IharaIota.html#L111) are the two degeneracy homomorphisms $\Gamma_0(Nq) \to \Gamma_0(N)$. Let $\ell$ be a nonzero prime with $\ell \nmid N$ (the case $\ell = q$ is allowed). The conclusion is that $\varphi$ and $\psi$ are both fixed by $\mathrm{heckeOperatorHom}$ with eigenvalue $\ell+1$: $\mathrm{heckeOperatorHom}\,N\,\ell\,A\,\varphi = (\ell+1)\cdot\varphi$ and likewise for $\psi$. Here [`HeckeEis.heckeOperatorHom N ℓ A`](def/Gamma0HeckeOperatorHom.html#L285) is the endomorphism of $\mathrm{Hom}(\Gamma_0(N),A)$ obtained by first pulling back along the conjugation homomorphism `heckeConj N ℓ`, from the finite-index subgroup `heckeUpper N ℓ` of $\Gamma_0(N)$ (the elements of $\Gamma_0(N)$ lying in `heckeUpperSL ℓ`) into $\Gamma_0(N)$, and then applying the group-transfer (corestriction) map `coresHom`, which sends a homomorphism on the subgroup to $g \mapsto \sum_{x \in \Gamma_0(N)/\mathrm{heckeUpper}(N,\ell)} \varphi(\mathrm{transferAux}\,g\,x)$.
--
--   This is the statement that the kernel of the level-raising map $\mathrm{Hom}(\Gamma_0(N),A)^2 \to \mathrm{Hom}(\Gamma_0(Nq),A)$ given by the two degeneracy maps is Eisenstein: every member of a kernel pair is an eigenvector of every $T_\ell$ with $\ell \nmid N$ and eigenvalue $\ell+1$, in the $\mathrm{Hom}$ (weight-two, trivial-coefficient $H^1$) formulation. It is used in the level-raising part of the argument, where it feeds the description of the $q$-new support of a normalised eigenform at an odd prime.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HeckeEis_heckeOperatorHom_eq_of_levelRaisingKernel.lean

import Definitions.Def_Gamma0HeckeOperatorHom
import Definitions.Def_Gamma0UnitsChar
import Definitions.Def_IharaIota

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem HeckeEis.heckeOperatorHom_eq_of_levelRaisingKernel (N q : ℕ) (hq : q.Prime) (hqN : ¬ q ∣ N)
    (A : Type*) [AddCommGroup A]
    (h2 : ∀ a : A, a + a = 0 → a = 0) (h3 : ∀ a : A, a + a + a = 0 → a = 0)
    (φ ψ : Additive (CongruenceSubgroup.Gamma0 N) →+ A)
    (hker : ∀ γ : CongruenceSubgroup.Gamma0 (N * q), φ (Ihara.ι₀ N q γ) + ψ (Ihara.ι₁ N q γ) = 0)
    {ℓ : ℕ} [NeZero ℓ] (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) :
    HeckeEis.heckeOperatorHom N ℓ A φ = (ℓ + 1) • φ ∧ HeckeEis.heckeOperatorHom N ℓ A ψ = (ℓ + 1) • ψ := by sorry
