-- Prove2me | Theorems.Thm_ModularCurve_hasLowerLevelTorsion_jZero_of_isPeuRamifieeAt_of_five_le
-- name    : ModularCurve.hasLowerLevelTorsion_jZero_of_isPeuRamifieeAt_of_five_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.414366+00:00
-- url     : https://prove2.me/theorems/0db53e8b-9e9d-542a-a1c4-3484388f85e7
-- title:
--   Mazur's principle at p for J₀(N₀p), p ≥ 5
-- statement:
--   Let $N_0 \ge 1$ and let $p$ be a prime with $p \ne 2$, $p \ge 5$ and $p \nmid N_0$. Assume the predicates [`ModularCurve.HeckeInputsAll`](def/ModularCurve_HeckeInputsAll.html#L8) at the levels $N_0 p$ and $N_0$, and that at each of these two levels the operators `heckeOperatorBar` commute pairwise, so that the Hecke algebra [`ModularCurve.HeckeAlg`](def/HeckeGalois_EichlerShimura.html#L14) $= \mathbb{Z}[X_\ell : \ell \text{ prime}]$ acts on $J_0 =$ [`ModularCurve.JZero`](def/ModularCurve_ArithmeticGalois.html#L115), the degree-zero divisor class group of the modular function field of the given level over $\overline{\mathbb{Q}}$, through [`ModularCurve.heckeModuleBar`](def/ModularCurve_HeckeModule.html#L82). Let $W$ be a Weierstrass curve over $\mathbb{Z}$ with $\Delta_W \ne 0$, semistable at $p$ in the sense that $p \mid \Delta_W$ implies $p \nmid c_4(W)$, whose $p$-torsion over $\overline{\mathbb{Q}}$ is irreducible (it is non-trivial and its only Galois-stable $\mathbb{Z}/p$-submodules are $0$ and itself), and which is peu ramifiée at $p$, meaning $p \mid v_p(\Delta_W)$ for the base change of $W$ to $\mathbb{Q}$. Let $S$ be the finite set of primes $\ell$ with $\ell \mid N_0 \, p \, |\Delta_W|$, and let $\mathfrak{m}$ be a maximal ideal of [`ModularCurve.HeckeAlg`](def/HeckeGalois_EichlerShimura.html#L14) containing $p$ and containing $X_\ell - a_\ell(W)$ for every prime $\ell \notin S$, where $a_\ell(W) = \ell + 1 - \#(W \bmod \ell)$ is `apOfModel`. Assume finally that the $\mathfrak{m}$-torsion submodule of $J_0(N_0 p)$ is non-zero. Then [`ModularCurve.HasLowerLevelTorsion`](def/ModularCurve_MazurPrincipleCore.html#L61) holds for $S$, $\mathfrak{m}$ and $J_0(N_0)$: there is a non-zero $y \in J_0(N_0)$ with $n \cdot y = 0$ for every natural number $n$ whose image lies in $\mathfrak{m}$, and $(X_\ell - b) \cdot y = 0$ for every prime $\ell \notin S$ and every $b \in \mathbb{Z}$ with $X_\ell - b \in \mathfrak{m}$.
--
--   This is the level-lowering step at the prime $p$ exactly dividing the level (Mazur's principle in Ribet's form): an irreducible eigensystem occurring in $J_0(N_0p)$ and peu ramifiée at $p$ already occurs, away from $S$, in the $\mathfrak{m}$-torsion of $J_0(N_0)$. It is used in the derivation that the mod-$p$ representation attached to $W$ is residually modular of the divided level $N_0$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_hasLowerLevelTorsion_jZero_of_isPeuRamifieeAt_of_five_le.lean

import Mathlib
import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_ModularCurve_HeckeInputsAll
import Definitions.Def_ModularCurve_MazurPrincipleCore
import Definitions.Def_FLTPrelim_ModularRep
import Definitions.Def_WeierstrassCurve_PeuRamifiee

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularCurve.hasLowerLevelTorsion_jZero_of_isPeuRamifieeAt_of_five_le
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] [NeZero p] (hp2 : p ≠ 2) (hp5 : 5 ≤ p) (hpN₀ : ¬ p ∣ N₀)
    (hinP : ModularCurve.HeckeInputsAll (N₀ * p))
    (hcommP : ModularCurve.HeckeOperatorsCommuteBar (N₀ * p))
    (hin : ModularCurve.HeckeInputsAll N₀) (hcomm : ModularCurve.HeckeOperatorsCommuteBar N₀)
    (W : WeierstrassCurve ℤ) (hΔ : W.Δ ≠ 0)
    (hsemi : (p : ℤ) ∣ W.Δ → ¬ (p : ℤ) ∣ W.c₄)
    (hirr : W.ModRepIsIrreducible p)
    (hfin : (W.map (Int.castRingHom ℚ)).IsPeuRamifieeAt p p)
    (S : Finset Nat.Primes) (hS : ∀ ℓ : Nat.Primes, ℓ ∈ S ↔ (ℓ : ℕ) ∣ N₀ * p * W.Δ.natAbs)
    (𝔪 : Ideal ModularCurve.HeckeAlg) (hmax : 𝔪.IsMaximal) (hp𝔪 : (p : ModularCurve.HeckeAlg) ∈ 𝔪)
    (hcong : ∀ ℓ : Nat.Primes, ℓ ∉ S →
      ModularCurve.heckeGen ℓ - MvPolynomial.C (W.apOfModel ℓ) ∈ 𝔪)
    (hocc : letI := ModularCurve.heckeModuleBar (N₀ * p);
      ModularCurve.heckeTorsion (ModularCurve.JZero (N₀ * p)) 𝔪 ≠ ⊥) :
    letI := ModularCurve.heckeModuleBar N₀
    ModularCurve.HasLowerLevelTorsion S 𝔪 (ModularCurve.JZero N₀) := by sorry
