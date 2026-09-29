-- Prove2me | Theorems.Thm_ModularCurve_exists_tateGaloisRep_frobenius_sub_U_mul_diamond_smul_eq_cyclotomicCharacter_smul_of_isFrobeniusAt_cornerSubmodule_tateModule_jH_of_ordinary
-- name    : ModularCurve.exists_tateGaloisRep_frobenius_sub_U_mul_diamond_smul_eq_cyclotomicCharacter_smul_of_isFrobeniusAt_cornerSubmodule_tateModule_jH_of_ordinary
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.061738+00:00
-- url     : https://prove2.me/theorems/19feae3a-4e41-568c-b364-d86da8058002
-- title:
--   Frobenius at p acts as Uₚ⟨ d⟩ on ordinary corner
-- statement:
--   Let $p$ be an odd prime, let $M \geq 1$ satisfy $p \mid M$ and $p^{2} \nmid M$, and let $H \leq (\mathbb{Z}/M)^{\times}$ be a subgroup containing every unit whose image under reduction $(\mathbb{Z}/M)^{\times} \to (\mathbb{Z}/(M/p))^{\times}$ is $1$. Let $S \subseteq \mathbb{N}$ be arbitrary, and assume [`ModularCurve.HeckeDiamondInputsHAll M H`](def/ModularCurve_XHOperators.html#L113): the predicate `HeckeInputsHAlong` over $\overline{\mathbb{Q}}$ holds for every prime $\ell$, and for each $d \in (\mathbb{Z}/M)^{\times}$ some $\overline{\mathbb{Q}}$-automorphism $\sigma$ of the function field `xHFunctionFieldBar M H` satisfies `IsDiamondAutHBar M H d σ`. Write $T =$ [`TateModule p (JH M H)`](def/EllipticCurve_TateModule.html#L15), the group of sequences $(x_n)$ in the degree-zero divisor class group $J_H =$ `Pic0` of that function field with $p^{n}x_n = 0$ and $p\,x_{n+1} = x_n$. Let $\mathbb{T}$ be a commutative $\mathbb{Z}_p$-algebra acting on $T$ compatibly with $\mathbb{Z}_p$ and faithfully (any $t$ annihilating all of $T$ is $0$), and let $op$ assign to each generator $g$ of [`CohCarrier.Gen M S`](def/CohCarrier_Inst.html#L13) — the symbols $T_\ell$ ($\ell$ prime, $\ell \notin S$, $\ell \nmid M$), $U_q$ ($q$ prime, $q \mid M$) and $\langle d \rangle$ ($d \in (\mathbb{Z}/M)^{\times}$) — an element of $\mathbb{T}$ acting on $T$ as the endomorphism `tateGenOpH M H S p g` induced by $g$ on $J_H$, with $\mathbb{Z}_p[\mathrm{range}\,op] = \mathbb{T}$. Let $S'$ be an [`IharaLemma.IdempotentSplitting`](def/IharaLemma_IdempotentSplitting.html#L7) of $\mathbb{T}$: finitely many idempotents $e_i$ forming a complete orthogonal family together with maximal ideals $\mathfrak{m}_i$ exhausting all maximal ideals and satisfying $e_i \in \mathfrak{m}_j \iff i \neq j$. Fix an index $i_0$ with $op(U_p) \notin \mathfrak{m}_{i_0}$ (the ordinarity hypothesis). Let $P\ell$ be a valuation subring of $\overline{\mathbb{Q}}$ with $p$ a non-unit of $P\ell$, and let $\varphi$ be a $\mathbb{Q}$-automorphism of $\overline{\mathbb{Q}}$ lying in the decomposition subgroup of $P\ell$ and acting on its residue field by $x \mapsto x^{p}$. Then there is $d \in (\mathbb{Z}/M)^{\times}$ such that for every $\tau$ in the image in $\mathrm{Aut}_{\mathbb{Q}}(\overline{\mathbb{Q}})$ of the inertia subgroup of $P\ell$, and every $x$ in the corner submodule $e_{i_0} \cdot T$, the element $y = \rho(\varphi)x - \big(op(U_p)\,op(\langle d\rangle)\big)\cdot x$, with $\rho =$ [`ModularCurve.JH.tateGaloisRep M H p`](def/ModularCurve_XH.html#L154), satisfies $\rho(\tau)y = \chi_p(\tau)\,y$, where $\chi_p$ is the $p$-adic cyclotomic character of $\overline{\mathbb{Q}}$ viewed in $\mathbb{Z}_p$.
--
--   This is the statement that on an ordinary local factor of the $p$-adic Tate module of $J_H(M)$, with $p$ exactly dividing the level, an arithmetic Frobenius at $p$ agrees with $U_p$ times a diamond operator modulo the part of the module on which inertia at $p$ acts through the cyclotomic character — the multiplicative, or toric, part. It is used in the construction of the two characters describing the restriction to a decomposition group at $p$ of the Galois action on such an ordinary corner.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_tateGaloisRep_frobenius_sub_U_mul_diamond_smul_eq_cyclotomicCharacter_smul_of_isFrobeniusAt_cornerSubmodule_tateModule_jH_of_ordinary.lean

import Mathlib
import Definitions.Def_ModularCurve_XHOperators
import Definitions.Def_IharaLemma_IdempotentSplitting
import Definitions.Def_EllipticCurve_FrobeniusTrace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularCurve.exists_tateGaloisRep_frobenius_sub_U_mul_diamond_smul_eq_cyclotomicCharacter_smul_of_isFrobeniusAt_cornerSubmodule_tateModule_jH_of_ordinary
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) (M : ℕ) [NeZero M] (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (H : Subgroup (ZMod M)ˣ)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (S : Set ℕ) (hin : ModularCurve.HeckeDiamondInputsHAll M H)
    {𝕋 : Type} [CommRing 𝕋] [Algebra ℤ_[p] 𝕋] [Module 𝕋 (TateModule p (ModularCurve.JH M H))]
    [IsScalarTower ℤ_[p] 𝕋 (TateModule p (ModularCurve.JH M H))]
    (hfaith : ∀ t : 𝕋, (∀ x : TateModule p (ModularCurve.JH M H), t • x = 0) → t = 0)
    (op : CohCarrier.Gen M S → 𝕋)
    (hop : ∀ (g : CohCarrier.Gen M S) (x : TateModule p (ModularCurve.JH M H)),
      op g • x = ModularCurve.tateGenOpH M H S p g x)
    (hgen : Algebra.adjoin ℤ_[p] (Set.range op) = ⊤)
    (S' : IharaLemma.IdempotentSplitting 𝕋) (i₀ : Fin S'.n)
    (hord : op (CohCarrier.Gen.U p Fact.out hpM) ∉ S'.𝔪 i₀)
    (Pl : ValuationSubring (AlgebraicClosure ℚ)) (hPl : Pl.LiesOverPrime p)
    (φ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hφ : Pl.IsFrobeniusAt φ p) :
    ∃ d : (ZMod M)ˣ, ∀ τ ∈ Pl.inertiaSubgroupIn ℚ,
      ∀ x ∈ IharaLemma.cornerSubmodule (M := TateModule p (ModularCurve.JH M H)) (S'.e i₀),
        ModularCurve.JH.tateGaloisRep M H p τ
            (ModularCurve.JH.tateGaloisRep M H p φ x -
              (op (CohCarrier.Gen.U p Fact.out hpM) * op (CohCarrier.Gen.dia d)) • x) =
          ((cyclotomicCharacter (AlgebraicClosure ℚ) p τ.toRingEquiv : ℤ_[p]ˣ) : ℤ_[p]) •
            (ModularCurve.JH.tateGaloisRep M H p φ x -
              (op (CohCarrier.Gen.U p Fact.out hpM) * op (CohCarrier.Gen.dia d)) • x) := by sorry
