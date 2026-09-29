-- Prove2me | Theorems.Thm_ModularCurve_exists_ordinaryFiltration_heckeTorsion_jZero_of_heckeGen_notMem_of_ne_two
-- name    : ModularCurve.exists_ordinaryFiltration_heckeTorsion_jZero_of_heckeGen_notMem_of_ne_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:51.361078+00:00
-- url     : https://prove2.me/theorems/8bc838c5-7616-565e-95af-a3d2efbcbb3a
-- title:
--   Multiplicative–étale filtration of 𝔪-torsion on J₀(N) at p
-- statement:
--   Let $N$ be a positive integer and $p$ a prime with $p \nmid N$ and $p \neq 2$. Let `HeckeAlg` be the polynomial ring $\mathbb Z[X_\ell : \ell \text{ prime}]$, and let $\mathfrak m$ be a maximal ideal of it containing the image of $p$ but not containing the generator `heckeGen` attached to $p$, that is $X_p \notin \mathfrak m$. Let `JZero N` be the degree-zero divisor class group (degree-zero divisors modulo principal divisors) of the modular function field of level $N$ base changed to $\overline{\mathbb Q} =$ `AlgebraicClosure ℚ`, equipped with the `HeckeAlg`-module structure `heckeModuleBar N` in which $X_\ell$ acts by the $\ell$-th Hecke operator, and assume the hypothesis that this action commutes with the natural action of $\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$. Let $P$ be a valuation subring of $\overline{\mathbb Q}$ with $p$ a non-unit of $P$. Then there is a submodule $C$ of the $\mathfrak m$-torsion $\{w : \mathfrak m w = 0\}$ of `JZero N` over the residue field $\mathrm{HeckeAlg}/\mathfrak m$ such that: (i) $C$ is stable under the decomposition subgroup of $P$ over $\mathbb Q$, acting through `mTorsionGaloisRep`; (ii) if $\sigma$ lies in the image of the inertia subgroup of $P$ and $a \in \mathbb N$ satisfies $\sigma\mu = \mu^a$ for every $\mu$ with $\mu^p = 1$, then $\sigma$ acts on $C$ as multiplication by the class of $a$; (iii) for every such inertia element $\sigma$ and every $\mathfrak m$-torsion point $w$ one has $\sigma w - w \in C$; and (iv) for every $\sigma$ lying in the decomposition subgroup and acting on the residue field of $P$ by $x \mapsto x^p$, and every $\mathfrak m$-torsion point $w$, one has $\sigma w - \overline{X_p}\, w \in C$.
--
--   This is the geometric input of the ordinary case: when $T_p$ is invertible modulo $\mathfrak m$, the $\mathfrak m$-torsion of the Jacobian of $X_0(N)$ carries a two-step filtration whose sub is of multiplicative type (inertia acting through the mod-$p$ cyclotomic character) and whose quotient is unramified with Frobenius acting as $T_p$, by the Eichler–Shimura congruence relation. It is used in the weight-two step of the construction of a stable line, [`GaloisRep.exists_conj_map_stableLine_of_theta_T_ne_zero_of_absolutelyIrreducible_of_eq_two`](thm.html#GaloisRep.exists_conj_map_stableLine_of_theta_T_ne_zero_of_absolutelyIrreducible_of_eq_two).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_ordinaryFiltration_heckeTorsion_jZero_of_heckeGen_notMem_of_ne_two.lean

import Definitions.Def_ModularCurve_HeckeModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ModularCurve.exists_ordinaryFiltration_heckeTorsion_jZero_of_heckeGen_notMem_of_ne_two
    (N : ℕ) [NeZero N] (p : ℕ) [Fact p.Prime] (hpN : ¬ p ∣ N) (hp2 : p ≠ 2)
    (𝔪 : Ideal HeckeAlg) (h𝔪 : 𝔪.IsMaximal) (hp𝔪 : ((p : ℕ) : HeckeAlg) ∈ 𝔪)
    (hord : heckeGen ⟨p, Fact.out⟩ ∉ 𝔪)
    (hsmc : letI := heckeModuleBar N
      SMulCommClass (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) HeckeAlg (JZero N))
    (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime p) :
    letI := heckeModuleBar N; haveI := hsmc
    ∃ C : Submodule (HeckeAlg ⧸ 𝔪) (heckeTorsion (JZero N) 𝔪),
      (∀ σ ∈ P.decompositionSubgroup ℚ, ∀ w ∈ C, mTorsionGaloisRep (JZero N) 𝔪 σ w ∈ C) ∧
      (∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ a : ℕ,
        (∀ μ : AlgebraicClosure ℚ, μ ^ p = 1 → σ μ = μ ^ a) →
          ∀ w ∈ C, mTorsionGaloisRep (JZero N) 𝔪 σ w = (a : HeckeAlg ⧸ 𝔪) • w) ∧
      (∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ w : heckeTorsion (JZero N) 𝔪,
        mTorsionGaloisRep (JZero N) 𝔪 σ w - w ∈ C) ∧
      (∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, P.IsFrobeniusAt σ p →
        ∀ w : heckeTorsion (JZero N) 𝔪,
          mTorsionGaloisRep (JZero N) 𝔪 σ w - Ideal.Quotient.mk 𝔪 (heckeGen ⟨p, Fact.out⟩) • w ∈ C) := by sorry
