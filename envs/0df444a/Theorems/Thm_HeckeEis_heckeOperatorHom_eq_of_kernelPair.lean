-- Prove2me | Theorems.Thm_HeckeEis_heckeOperatorHom_eq_of_kernelPair
-- name    : HeckeEis.heckeOperatorHom_eq_of_kernelPair
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.342414+00:00
-- url     : https://prove2.me/theorems/5a2c92ea-0532-5c19-9e15-b21aae2b475b
-- title:
--   Kernel pairs of level raising are Eisenstein, given Ihara
-- statement:
--   Fix as a hypothesis the following Ihara-type statement, quantified over all data in a fixed universe: for every $N$ and every prime $q \nmid N$, every abelian group $A$ in which $a+a=0$ implies $a=0$ and $a+a+a=0$ implies $a=0$, and every pair of additive homomorphisms $\varphi,\psi \colon \mathrm{Additive}(\Gamma_0(N)) \to A$ satisfying $\varphi(\mathtt{Ihara.\iota_0}\,N\,q\,\gamma) + \psi(\mathtt{Ihara.\iota_1}\,N\,q\,\gamma) = 0$ for all $\gamma \in \Gamma_0(Nq)$ (where [`Ihara.ι₀ N q`](def/IharaIota.html#L17) and [`Ihara.ι₁ N q`](def/IharaIota.html#L111) are the two maps $\Gamma_0(Nq) \to \mathrm{Additive}(\Gamma_0(N))$ used throughout), both $\varphi$ and $\psi$ factor as $\chi \circ$ [`Ihara.gamma0UnitsChar N`](def/Gamma0UnitsChar.html#L13), the additive form of the units-valued character $\Gamma_0(N) \to (\mathbb{Z}/N)^\times$ obtained from `Gamma0Map N`, for some additive homomorphism $\chi$ on $\mathrm{Additive}((\mathbb{Z}/N)^\times)$. Given such data — $N$, a prime $q \nmid N$, a group $A$ without the above $2$- and $3$-torsion, and $\varphi, \psi$ with $\varphi \circ \iota_0 + \psi \circ \iota_1 = 0$ on $\Gamma_0(Nq)$ — and given a prime $\ell \nmid N$, the conclusion is that [`HeckeEis.heckeOperatorHom N ℓ A`](def/Gamma0HeckeOperatorHom.html#L285) (the composite of restriction along the conjugation homomorphism `heckeConj N ℓ` on the subgroup `heckeUpper N ℓ` with the transfer-type corestriction back to $\Gamma_0(N)$) sends $\varphi$ to $(\ell+1)\varphi$ and $\psi$ to $(\ell+1)\psi$.
--
--   This is the statement, at the level of $A$-valued homomorphisms on $\Gamma_0(N)$, that the kernel of the level-raising map $\mathrm{Hom}(\Gamma_0(N),A)^2 \to \mathrm{Hom}(\Gamma_0(Nq),A)$ is Eisenstein: the Hecke operator $T_\ell$ acts on both members by $\ell+1$. Ihara's lemma enters only as an explicit hypothesis, so the result is a conditional implication; it feeds the level-raising kernel statement [`HeckeEis.heckeOperatorHom_eq_of_levelRaisingKernel`](thm.html#HeckeEis.heckeOperatorHom_eq_of_levelRaisingKernel). Note that the conclusion is asserted for every prime $\ell \nmid N$, the case $\ell = q$ included.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HeckeEis_heckeOperatorHom_eq_of_kernelPair.lean

import Definitions.Def_Gamma0HeckeOperatorHom
import Definitions.Def_Gamma0UnitsChar
import Definitions.Def_IharaIota

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

theorem HeckeEis.heckeOperatorHom_eq_of_kernelPair
    (ihara : ∀ (N q : ℕ) (_ : q.Prime) (_ : ¬ q ∣ N) (A : Type u) [AddCommGroup A]
      (_ : ∀ a : A, a + a = 0 → a = 0) (_ : ∀ a : A, a + a + a = 0 → a = 0)
      (φ ψ : Additive (CongruenceSubgroup.Gamma0 N) →+ A)
      (_ : ∀ γ : CongruenceSubgroup.Gamma0 (N * q), φ (Ihara.ι₀ N q γ) + ψ (Ihara.ι₁ N q γ) = 0),
      (∃ χ : Additive (ZMod N)ˣ →+ A, φ = χ.comp (Ihara.gamma0UnitsChar N)) ∧
      (∃ χ : Additive (ZMod N)ˣ →+ A, ψ = χ.comp (Ihara.gamma0UnitsChar N)))
    (N q : ℕ) (hq : q.Prime) (hqN : ¬ q ∣ N)
    (A : Type u) [AddCommGroup A]
    (h2 : ∀ a : A, a + a = 0 → a = 0) (h3 : ∀ a : A, a + a + a = 0 → a = 0)
    (φ ψ : Additive (CongruenceSubgroup.Gamma0 N) →+ A)
    (hker : ∀ γ : CongruenceSubgroup.Gamma0 (N * q), φ (Ihara.ι₀ N q γ) + ψ (Ihara.ι₁ N q γ) = 0)
    {ℓ : ℕ} [NeZero ℓ] (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N) :
    HeckeEis.heckeOperatorHom N ℓ A φ = (ℓ + 1) • φ ∧ HeckeEis.heckeOperatorHom N ℓ A ψ = (ℓ + 1) • ψ := by sorry
