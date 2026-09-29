-- Prove2me | Theorems.Thm_ModularCurve_exists_addMonoidHom_torsion_ssPolarDifferentials_dlog_of_ordinary_of_mem_infSubgroup
-- name    : ModularCurve.exists_addMonoidHom_torsion_ssPolarDifferentials_dlog_of_ordinary_of_mem_infSubgroup
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.209688+00:00
-- url     : https://prove2.me/theorems/c03f1983-3328-5dda-8825-01318f48e8fd
-- title:
--   Hecke-equivariant dlog from J_H[p] to supersingular polar differentials
-- statement:
--   Fix an odd prime $p$ and $M \neq 0$ with $p \mid M$ and $p^2 \nmid M$, and a subgroup $H \le (\mathbb{Z}/M)^\times$ containing every unit whose image in $(\mathbb{Z}/(M/p))^\times$ is trivial; let $S \subseteq \mathbb{N}$, and assume [`ModularCurve.HeckeDiamondInputsHAll M H`](def/ModularCurve_XHOperators.html#L113), i.e. the Hecke input package at every prime together with the existence, for each $d \in (\mathbb{Z}/M)^\times$, of a diamond automorphism of $\overline{\mathbb{Q}} \cdot X_H(M)$'s $q$-expansion function field. Let $\mathbb{T}$ be a commutative $\mathbb{Z}_p$-algebra acting on the Tate module $T_p J_H$, where $J_H = \mathrm{Pic}^0$ of the base-changed function field $\overline{\mathbb{Q}} \cdot X_H(M)$, compatibly with the $\mathbb{Z}_p$-action and faithfully, with a map $\mathrm{op}$ from the generators $T_\ell$ ($\ell$ prime, $\ell \notin S$, $\ell \nmid M$), $U_q$ ($q \mid M$), $\langle d \rangle$ to $\mathbb{T}$ such that $\mathrm{op}\,g$ acts as the induced endomorphism `tateGenOpH` of $g$ on $T_p J_H$, and with $\mathbb{Z}_p[\mathrm{op}] = \mathbb{T}$. Let $S'$ be an idempotent splitting of $\mathbb{T}$ (complete orthogonal idempotents $e_i$ and maximal ideals $\mathfrak{m}_i$ exhausting the maximal spectrum, with $e_i \in \mathfrak{m}_j \iff i \neq j$), let $i_0$ be an index with $\mathrm{op}(U_p) \notin \mathfrak{m}_{i_0}$, and let $\mathit{Pl}$ be a valuation subring of $\overline{\mathbb{Q}}$ with $p$ in its nonunits. Let $P_0$ be a $\mathbb{T}$-submodule of $T_p J_H$ consisting exactly of the elements of the corner submodule $e_{i_0} \cdot T_p J_H$ on which the inertia subgroup of $\mathit{Pl}$ over $\mathbb{Q}$ acts through the cyclotomic character at $p$. Let $K$ be an algebraically closed field of characteristic $p$, and let $\tau$ be a ring homomorphism from $\mathbb{T}$ to the $K$-endomorphisms of $\Omega_1 :=$ `ssPolarDifferentials` $K\,\Gamma_{H'}(M/p)\,p$ — the differentials of the $q$-expansion function field of level $\Gamma_{H'}(M/p)$, $H'$ the image of $H$, that are regular away from the supersingular places and have at most simple poles there — such that each $\tau(\mathrm{op}\,g)$ acts as `genDiffModL` $g$ (the Hecke correspondence operator for $T_\ell$ and for $U_q$ with $q \neq p$, the Frobenius push-forward for $U_p$, the diamond pullback for $\langle d \rangle$). Finally let $d \in (\mathbb{Z}/M)^\times$ have image $p$ in $\mathbb{Z}/(M/p)$, with that image or its negative lying in $H'$. Then there is an additive homomorphism $\Theta$ from the $p$-torsion of $\mathrm{Pic}^0(\overline{\mathbb{Q}} \cdot X_H(M))$ to $\Omega_1$ such that: (i) whenever $y = \mathrm{genOpH}\,g\,x$ in $J_H$ for torsion points $x,y$ and a generator $g$, one has $\Theta y =$ `genDiffModL` $g\,(\Theta x)$ in $\Omega[\cdot\,\!/K]$; (ii) for $x$ whose class lies in the image of the corner submodule $e_{i_0} \cdot T_p J_H$ under the first projection $T_p J_H \to J_H$, $\Theta x = 0$ if and only if for every $\sigma$ in the inertia subgroup of $\mathit{Pl}$ over $\mathbb{Q}$ and every $c \in \mathbb{N}$ with $\sigma \zeta = \zeta^c$ for all $p$-th roots of unity $\zeta$, one has $\sigma \cdot x = c \cdot x$; (iii) the $K$-span of the image under $\Theta$ of that set of $x$ equals the range of $\tau(e_{i_0})$; and (iv) the cardinality of the image of $e_{i_0} \cdot T_p J_H$ in $J_H$ equals the number of its elements killed by $\Theta$ times $p^{\dim_K \mathrm{range}\,\tau(e_{i_0})}$.
--
--   This is the Atkin–Lehner-twisted logarithmic derivative map of the ordinary part of $J_H(M)[p]$ into the differentials with at most simple supersingular poles at level $M/p$ in characteristic $p$, together with its kernel description by cyclotomic inertia, its Hecke equivariance, the spanning of the $e_{i_0}$-part of the differentials, and the resulting index formula. It feeds the construction of a linear isomorphism identifying the corner of $J_H(M)[p]$ modulo its multiplicative part with the dual of the relevant space of differentials, used in the level-lowering input to modularity lifting.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_addMonoidHom_torsion_ssPolarDifferentials_dlog_of_ordinary_of_mem_infSubgroup.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDifferentialsModL
import Definitions.Def_ModularCurve_XHOperators
import Definitions.Def_IharaLemma_IdempotentSplitting
import Definitions.Def_EllipticCurve_FrobeniusTrace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularCurve.exists_addMonoidHom_torsion_ssPolarDifferentials_dlog_of_ordinary_of_mem_infSubgroup
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
    (P0 : Submodule 𝕋 (TateModule p (ModularCurve.JH M H)))
    (hP0 : ∀ x : TateModule p (ModularCurve.JH M H), x ∈ P0 ↔
      x ∈ IharaLemma.cornerSubmodule (M := TateModule p (ModularCurve.JH M H)) (S'.e i₀) ∧
        ∀ σ ∈ Pl.inertiaSubgroupIn ℚ, ModularCurve.JH.tateGaloisRep M H p σ x =
          ((cyclotomicCharacter (AlgebraicClosure ℚ) p σ.toRingEquiv : ℤ_[p]ˣ) : ℤ_[p]) • x)
    (K : Type*) [Field K] [IsAlgClosed K] [Algebra (ZMod p) K]
    (τ : 𝕋 →+* Module.End K
      (ModularCurve.ssPolarDifferentials K
        (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p))
    (hτ : ∀ (g : CohCarrier.Gen M S)
      (ω : ModularCurve.ssPolarDifferentials K
        (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p),
      ((τ (op g) ω : ModularCurve.ssPolarDifferentials K
          (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p) :
        Ω[ModularCurve.qExpFunctionFieldC K
            (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))⁄K]) =
        ModularCurve.genDiffModL K p M H hpM S g ω)

    (d : (ZMod M)ˣ) (hd : ((ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) d : (ZMod (M / p))ˣ) : ZMod (M / p)) = (p : ZMod (M / p)))
    (hdH : ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) d ∈ ModularCurve.infSubgroup p M H hpM ∨
      -ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) d ∈ ModularCurve.infSubgroup p M H hpM)
    :
    ∃ Θ : ↥(AlgebraicCurve.Pic0.torsion (AlgebraicClosure ℚ) (ModularCurve.xHFunctionFieldBar M H) p) →+ ModularCurve.ssPolarDifferentials K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p,

      (∀ (g : CohCarrier.Gen M S) (x y : ↥(AlgebraicCurve.Pic0.torsion (AlgebraicClosure ℚ) (ModularCurve.xHFunctionFieldBar M H) p)),
        (y : ModularCurve.JH M H) = ModularCurve.genOpH M H S g (x : ModularCurve.JH M H) →
          ((Θ y : ModularCurve.ssPolarDifferentials K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p) :
            Ω[ModularCurve.qExpFunctionFieldC K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM))⁄K]) =
            ModularCurve.genDiffModL K p M H hpM S g (Θ x)) ∧

      (∀ x : ↥(AlgebraicCurve.Pic0.torsion (AlgebraicClosure ℚ) (ModularCurve.xHFunctionFieldBar M H) p), (x : ModularCurve.JH M H) ∈
          ((IharaLemma.cornerSubmodule (M := TateModule p (ModularCurve.JH M H)) (S'.e i₀)).toAddSubgroup).map
              (TateModule.proj p (ModularCurve.JH M H) 1) →
        (Θ x = 0 ↔ ∀ σ ∈ Pl.inertiaSubgroupIn ℚ, ∀ c : ℕ,
          (∀ ζ : AlgebraicClosure ℚ, ζ ^ p = 1 → σ ζ = ζ ^ c) →
            σ • (x : ModularCurve.JH M H) = c • (x : ModularCurve.JH M H))) ∧

      Submodule.span K (Θ '' {x | (x : ModularCurve.JH M H) ∈
          ((IharaLemma.cornerSubmodule (M := TateModule p (ModularCurve.JH M H)) (S'.e i₀)).toAddSubgroup).map
              (TateModule.proj p (ModularCurve.JH M H) 1)}) =
        LinearMap.range (τ (S'.e i₀)) ∧

      Nat.card ↥(((IharaLemma.cornerSubmodule (M := TateModule p (ModularCurve.JH M H)) (S'.e i₀)).toAddSubgroup).map
              (TateModule.proj p (ModularCurve.JH M H) 1)) =
        Nat.card {x : ↥(AlgebraicCurve.Pic0.torsion (AlgebraicClosure ℚ) (ModularCurve.xHFunctionFieldBar M H) p) // (x : ModularCurve.JH M H) ∈
          ((IharaLemma.cornerSubmodule (M := TateModule p (ModularCurve.JH M H)) (S'.e i₀)).toAddSubgroup).map
              (TateModule.proj p (ModularCurve.JH M H) 1) ∧ Θ x = 0} *
          p ^ Module.finrank K ↥(LinearMap.range (τ (S'.e i₀))) := by sorry
