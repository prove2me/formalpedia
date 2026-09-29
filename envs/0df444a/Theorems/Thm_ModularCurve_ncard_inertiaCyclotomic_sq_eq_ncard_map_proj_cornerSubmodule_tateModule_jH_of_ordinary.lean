-- Prove2me | Theorems.Thm_ModularCurve_ncard_inertiaCyclotomic_sq_eq_ncard_map_proj_cornerSubmodule_tateModule_jH_of_ordinary
-- name    : ModularCurve.ncard_inertiaCyclotomic_sq_eq_ncard_map_proj_cornerSubmodule_tateModule_jH_of_ordinary
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.624895+00:00
-- url     : https://prove2.me/theorems/c54e2e83-6642-59d0-9b1b-eb0062a8db24
-- title:
--   Half-rank of the inertia-cyclotomic part of the ordinary corner
-- statement:
--   Let $p$ be an odd prime, let $M \ge 1$ be divisible by $p$ but not by $p^2$, and let $H \le (\mathbb{Z}/M)^\times$ be a subgroup containing every unit whose image in $(\mathbb{Z}/(M/p))^\times$ is trivial. Let $S$ be a set of natural numbers, and assume [`ModularCurve.HeckeDiamondInputsHAll M H`](def/ModularCurve_XHOperators.html#L113), i.e. the Hecke inputs along every prime $\ell$ for the base-changed function field of $X_H(M)$ over $\overline{\mathbb{Q}}$ together with, for each $d \in (\mathbb{Z}/M)^\times$, an automorphism satisfying `IsDiamondAutHBar`. Write $J = J_H(M)$ for the degree-zero divisor class group $\mathrm{Pic}^0$ of that function field and $T_p J$ for the Tate module, realised as the group of sequences $(x_n)_{n \in \mathbb{N}}$ in $J$ with $p^n x_n = 0$ and $p\,x_{n+1} = x_n$. Let $\mathbb{T}$ be a commutative $\mathbb{Z}_p$-algebra acting on $T_p J$ compatibly with the $\mathbb{Z}_p$-action and faithfully (an element killing every point of $T_p J$ is zero), and let $op$ assign to each generator symbol in [`CohCarrier.Gen M S`](def/CohCarrier_Inst.html#L13) — the symbols $T_\ell$ for primes $\ell \notin S$ with $\ell \nmid M$, $U_q$ for primes $q \mid M$, and $\langle d \rangle$ for $d \in (\mathbb{Z}/M)^\times$ — an element of $\mathbb{T}$ acting on $T_p J$ as the corresponding operator [`ModularCurve.tateGenOpH`](def/ModularCurve_XHOperators.html#L99), with $\mathbb{T}$ generated over $\mathbb{Z}_p$ by the image of $op$. Let $S'$ be an idempotent splitting of $\mathbb{T}$: a finite family of complete orthogonal idempotents $e_i$ together with maximal ideals $\mathfrak{m}_i$ exhausting the maximal ideals of $\mathbb{T}$ and satisfying $e_i \in \mathfrak{m}_j \iff i \ne j$. Fix an index $i_0$ with $op(U_p) \notin \mathfrak{m}_{i_0}$, and let $\mathrm{Pl}$ be a valuation subring of $\overline{\mathbb{Q}}$ with $p$ in its nonunits. Let $G$ be the image, under evaluation of a sequence at index $1$, of the additive subgroup underlying the corner submodule $e_{i_0} \cdot T_p J$. Then the square of the cardinality of the set of $x \in J$ lying in $G$ and such that $\sigma \cdot x = c\,x$ for every $\sigma$ in the inertia subgroup of $\mathrm{Pl}$ over $\mathbb{Q}$ (the image of the inertia subgroup inside the decomposition subgroup) and every natural number $c$ with $\sigma\zeta = \zeta^c$ for all $\zeta$ with $\zeta^p = 1$, equals the cardinality of $G$.
--
--   This is the equal-rank clause of the ordinary filtration on the $p$-adic Tate module of $J_H(M)$ in the ordinary corner cut out by an idempotent avoiding the maximal ideal containing $U_p$, stated at the first level: the inertia-cyclotomic (multiplicative) part of the mod-$p$ image of the corner has index equal to its own order, so it accounts for exactly half the rank. It feeds the subsequent analysis of the Néron model of $J_H(M)$ at $p$ and of multiplicative points versus polar differentials.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_ncard_inertiaCyclotomic_sq_eq_ncard_map_proj_cornerSubmodule_tateModule_jH_of_ordinary.lean

import Mathlib
import Definitions.Def_ModularCurve_XHOperators
import Definitions.Def_IharaLemma_IdempotentSplitting
import Definitions.Def_EllipticCurve_FrobeniusTrace
import Definitions.Def_FLTPrelim_Ramification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ModularCurve.ncard_inertiaCyclotomic_sq_eq_ncard_map_proj_cornerSubmodule_tateModule_jH_of_ordinary
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
    :
    Set.ncard {x : ModularCurve.JH M H |
        x ∈ ((IharaLemma.cornerSubmodule (M := TateModule p (ModularCurve.JH M H)) (S'.e i₀)).toAddSubgroup).map
        (TateModule.proj p (ModularCurve.JH M H) 1) ∧
        ∀ σ ∈ Pl.inertiaSubgroupIn ℚ, ∀ c : ℕ,
          (∀ ζ : AlgebraicClosure ℚ, ζ ^ p = 1 → σ ζ = ζ ^ c) → σ • x = c • x} ^ 2 =
      Nat.card ↥(((IharaLemma.cornerSubmodule (M := TateModule p (ModularCurve.JH M H)) (S'.e i₀)).toAddSubgroup).map
        (TateModule.proj p (ModularCurve.JH M H) 1)) := by sorry
