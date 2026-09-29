-- Prove2me | Theorems.Thm_Ihara_gamma0Fin_hom_factor
-- name    : Ihara.gamma0Fin_hom_factor
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.515241+00:00
-- url     : https://prove2.me/theorems/43511950-c5cf-59e5-8e57-f3953505bfa7
-- title:
--   Homomorphisms of Γ₀(N;ℤ/M) factor through the diagonal character
-- statement:
--   Let $N$ and $M$ be natural numbers with $M \neq 0$ and $N \mid M$. Write $\Gamma_0(N;\mathbb{Z}/M)$ for [`Ihara.Gamma0Fin N M`](def/IharaGamma0Fin.html#L14), the subgroup of $\mathrm{SL}_2(\mathbb{Z}/M)$ consisting of those matrices $g$ whose lower-left entry $g_{10}$ is divisible by the image of $N$ in $\mathbb{Z}/M$, and write [`Ihara.gamma0FinUnitsChar N M hNM`](def/IharaGamma0Fin.html#L59) for the homomorphism $\Gamma_0(N;\mathbb{Z}/M) \to (\mathbb{Z}/N)^{\times}$ obtained by passing to units from the monoid homomorphism [`Ihara.gamma0FinMap`](def/IharaGamma0Fin.html#L43) that sends $g$ to the reduction of the lower-right entry $g_{11}$ along the ring map $\mathbb{Z}/M \to \mathbb{Z}/N$ induced by $N \mid M$. Let $A$ be an additive abelian group satisfying two torsion hypotheses: $a + a = 0$ implies $a = 0$, and $a + a + a = 0$ implies $a = 0$, for all $a \in A$; that is, $A$ has no $2$-torsion and no $3$-torsion. Then for every group homomorphism $\Phi$ from $\Gamma_0(N;\mathbb{Z}/M)$ to the multiplicative copy `Multiplicative A` of $A$ there exists a homomorphism $\chi : (\mathbb{Z}/N)^{\times} \to \mathrm{Multiplicative}\,A$ with $\Phi$ equal to [`Ihara.gamma0FinUnitsChar N M hNM`](def/IharaGamma0Fin.html#L59) followed by $\chi$. No primality or further divisibility condition is imposed on $N$ or $M$.
--
--   The statement identifies all homomorphisms from the finite congruence group $\Gamma_0(N;\mathbb{Z}/M)$, the reduction modulo $M$ of $\Gamma_0(N)$, into an abelian group in which $6$ acts injectively: the abelianisation of $\Gamma_0(N;\mathbb{Z}/M)$ is controlled, away from $2$- and $3$-torsion, by the lower-right-entry character with values in $(\mathbb{Z}/N)^{\times}$. It is used in the corresponding factorisation statement [`Ihara.gamma0Away_hom_factor`](thm.html#Ihara.gamma0Away_hom_factor) for the groups arising in Ihara's lemma.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Ihara_gamma0Fin_hom_factor.lean

import Definitions.Def_IharaGamma0Fin

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem Ihara.gamma0Fin_hom_factor {N M : ℕ} [NeZero M] (hNM : N ∣ M) {A : Type*} [AddCommGroup A]
    (h2 : ∀ a : A, a + a = 0 → a = 0) (h3 : ∀ a : A, a + a + a = 0 → a = 0)
    (Φ : Ihara.Gamma0Fin N M →* Multiplicative A) :
    ∃ χ : (ZMod N)ˣ →* Multiplicative A, Φ = χ.comp (Ihara.gamma0FinUnitsChar N M hNM) := by sorry
