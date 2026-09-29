-- Prove2me | Theorems.Thm_ModularCurve_exists_U_mul_diamond_smul_tateGaloisRep_frobenius_eq_cyclotomicCharacter_smul_of_forall_inertia_cornerSubmodule_tateModule_jH_of_ordinary
-- name    : ModularCurve.exists_U_mul_diamond_smul_tateGaloisRep_frobenius_eq_cyclotomicCharacter_smul_of_forall_inertia_cornerSubmodule_tateModule_jH_of_ordinary
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.209688+00:00
-- url     : https://prove2.me/theorems/99c31c10-470f-5c4f-a00a-c6ce6f113d47
-- title:
--   Frobenius on the multiplicative part of an ordinary factor
-- statement:
--   Let $p$ be an odd prime and $M\ge 1$ with $p\mid M$ but $p^2\nmid M$, and let $H\le(\mathbb Z/M)^\times$ be a subgroup containing every unit whose image under the reduction $(\mathbb Z/M)^\times\to(\mathbb Z/(M/p))^\times$ is $1$. Fix a set $S$ of natural numbers and assume [`ModularCurve.HeckeDiamondInputsHAll M H`](def/ModularCurve_XHOperators.html#L113), i.e. the inputs `HeckeInputsHAlong` at every prime $\ell$ for the function field of $X_H$ over $\overline{\mathbb Q}$ together with, for each $d\in(\mathbb Z/M)^\times$, an automorphism of that field which is a diamond automorphism for $d$. Let $T=$ [`TateModule p (ModularCurve.JH M H)`](def/EllipticCurve_TateModule.html#L15) be the module of sequences $(x_n)$ in $\mathrm{Pic}^0$ of the base-changed function field of $X_H$ with $p^nx_n=0$ and $px_{n+1}=x_n$, and let $\mathbb T$ be a commutative $\mathbb Z_p$-algebra acting on $T$ compatibly with the $\mathbb Z_p$-action, faithfully (an element killing all of $T$ is zero), equipped with a map $op$ from the generators [`CohCarrier.Gen M S`](def/CohCarrier_Inst.html#L13) (symbols $T_\ell$ for primes $\ell\notin S$ with $\ell\nmid M$, $U_q$ for primes $q\mid M$, and $\langle d\rangle$ for $d\in(\mathbb Z/M)^\times$) to $\mathbb T$ such that $op(g)$ acts as the endomorphism [`ModularCurve.tateGenOpH M H S p g`](def/ModularCurve_XHOperators.html#L99), and with $\mathbb T$ generated over $\mathbb Z_p$ by the image of $op$. Let $S'$ be an idempotent splitting of $\mathbb T$: complete orthogonal idempotents $e_0,\dots,e_{n-1}$ and maximal ideals $\mathfrak m_i$ exhausting all maximal ideals, with $e_i\in\mathfrak m_j$ iff $i\ne j$; fix $i_0$ with $op(U_p)\notin\mathfrak m_{i_0}$ (ordinarity). Let $Pl$ be a valuation subring of $\overline{\mathbb Q}=$ `AlgebraicClosure ℚ` with $p$ a non-unit, and let $\varphi\in\mathrm{Gal}(\overline{\mathbb Q}/\mathbb Q)$ lie in its decomposition subgroup and act on the residue field by $x\mapsto x^p$. Then there is $d_0\in(\mathbb Z/M)^\times$ such that for every $x$ in the corner submodule $e_{i_0}T$ satisfying $\tau x=\varepsilon_p(\tau)x$ for all $\tau$ in the inertia subgroup of $Pl$ over $\mathbb Q$ (image of `inertiaSubgroup` in the Galois group, $\varepsilon_p$ the $p$-adic cyclotomic character), one has $\bigl(op(U_p)\,op(\langle d_0\rangle)\bigr)\cdot\varphi(x)=\varepsilon_p(\varphi)\,x$, where $\varphi$ acts through [`ModularCurve.JH.tateGaloisRep`](def/ModularCurve_XH.html#L154).
--
--   This is the multiplicative (μ-type) half of Wiles' local description at $p$ of an ordinary factor of $T_pJ_H(M)$ when $p$ exactly divides $M$: on the part of the corner $e_{i_0}T_pJ_H(M)$ on which inertia at $p$ acts by the cyclotomic character, arithmetic Frobenius acts as $\varepsilon_p(\varphi)\bigl(U_p\langle d_0\rangle\bigr)^{-1}$. It is used by the companion statement expressing $\varphi-U_p\langle d_0\rangle$ on the corner, which supplies the unramified-quotient form of the local shape at $p$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_U_mul_diamond_smul_tateGaloisRep_frobenius_eq_cyclotomicCharacter_smul_of_forall_inertia_cornerSubmodule_tateModule_jH_of_ordinary.lean

import Mathlib
import Definitions.Def_ModularCurve_XHOperators
import Definitions.Def_IharaLemma_IdempotentSplitting
import Definitions.Def_EllipticCurve_FrobeniusTrace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularCurve.exists_U_mul_diamond_smul_tateGaloisRep_frobenius_eq_cyclotomicCharacter_smul_of_forall_inertia_cornerSubmodule_tateModule_jH_of_ordinary
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
    ∃ d₀ : (ZMod M)ˣ,
      ∀ x ∈ IharaLemma.cornerSubmodule (M := TateModule p (ModularCurve.JH M H)) (S'.e i₀),
        (∀ τ ∈ Pl.inertiaSubgroupIn ℚ,
          ModularCurve.JH.tateGaloisRep M H p τ x =
            ((cyclotomicCharacter (AlgebraicClosure ℚ) p τ.toRingEquiv : ℤ_[p]ˣ) : ℤ_[p]) • x) →
        (op (CohCarrier.Gen.U p Fact.out hpM) * op (CohCarrier.Gen.dia d₀)) •
            ModularCurve.JH.tateGaloisRep M H p φ x =
          ((cyclotomicCharacter (AlgebraicClosure ℚ) p φ.toRingEquiv : ℤ_[p]ˣ) : ℤ_[p]) • x := by sorry
