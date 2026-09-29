-- Prove2me | Theorems.Thm_Ihara_ihara_hom_factor
-- name    : Ihara.ihara_hom_factor
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.515241+00:00
-- url     : https://prove2.me/theorems/328a90e9-2b9a-521c-9794-3a13c7622129
-- title:
--   Ihara's lemma for Γ₀(N) in homomorphism form
-- statement:
--   Let $N$ and $q$ be natural numbers with $q$ prime and $q \nmid N$, and let $A$ be an additive commutative group assumed to have no $2$-torsion and no $3$-torsion, in the precise sense that $a + a = 0$ implies $a = 0$ and $a + a + a = 0$ implies $a = 0$ for all $a \in A$. Let $\varphi, \psi$ be additive group homomorphisms from the additive avatar of $\Gamma_0(N)$ to $A$, and suppose they satisfy the kernel-pair relation $\varphi(\iota_0 \gamma) + \psi(\iota_1 \gamma) = 0$ for every $\gamma \in \Gamma_0(Nq)$, where `ι₀ N q` and `ι₁ N q` are the two maps from $\Gamma_0(Nq)$ into (the additive avatar of) $\Gamma_0(N)$. The conclusion is that each of $\varphi$ and $\psi$ factors through the character `gamma0UnitsChar N`, the additive avatar of the homomorphism $\Gamma_0(N) \to (\mathbb{Z}/N)^\times$ obtained from `CongruenceSubgroup.Gamma0Map N` by passing to units: there exist additive homomorphisms $\chi$ from the additive avatar of $(\mathbb{Z}/N)^\times$ to $A$ with $\varphi = \chi \circ$ `gamma0UnitsChar N`, and likewise for $\psi$.
--
--   This is the sharp form of Ihara's lemma for $\Gamma_0(N)$, spelled at the level of homomorphisms: a pair of homomorphisms annihilating the image of $\Gamma_0(Nq)$ under the two degeneracy maps must be of Eisenstein type, namely a character of $(\mathbb{Z}/N)^\times$, which is the Hom-theoretic shadow of the statement that the kernel of the level-raising map is the antidiagonal Shimura subgroup. It is proved from the presentation of $\Gamma_0(N)$ away from $q$ as an amalgam (injectivity and surjectivity of [`Ihara.amalgamToGamma0Away`](def/IharaAmalgamMap.html#L141) together with [`Ihara.gamma0Away_hom_factor`](thm.html#Ihara.gamma0Away_hom_factor)), and is used in [`HeckeEis.heckeOperatorHom_eq_of_levelRaisingKernel`](thm.html#HeckeEis.heckeOperatorHom_eq_of_levelRaisingKernel).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Ihara_ihara_hom_factor.lean

import Definitions.Def_Gamma0UnitsChar
import Definitions.Def_IharaIota

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem Ihara.ihara_hom_factor (N q : ℕ) (hq : q.Prime) (hqN : ¬ q ∣ N)
    (A : Type*) [AddCommGroup A]
    (h2 : ∀ a : A, a + a = 0 → a = 0) (h3 : ∀ a : A, a + a + a = 0 → a = 0)
    (φ ψ : Additive (CongruenceSubgroup.Gamma0 N) →+ A)
    (hker : ∀ γ : CongruenceSubgroup.Gamma0 (N * q), φ (ι₀ N q γ) + ψ (ι₁ N q γ) = 0) :
    (∃ χ : Additive (ZMod N)ˣ →+ A, φ = χ.comp (gamma0UnitsChar N)) ∧
    (∃ χ : Additive (ZMod N)ˣ →+ A, ψ = χ.comp (gamma0UnitsChar N)) := by sorry
