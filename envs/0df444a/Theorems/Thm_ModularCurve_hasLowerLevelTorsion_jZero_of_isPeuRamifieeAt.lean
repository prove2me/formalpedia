-- Prove2me | Theorems.Thm_ModularCurve_hasLowerLevelTorsion_jZero_of_isPeuRamifieeAt
-- name    : ModularCurve.hasLowerLevelTorsion_jZero_of_isPeuRamifieeAt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.414366+00:00
-- url     : https://prove2.me/theorems/a3d8ccc6-0ce1-5c49-bd1e-ce02343dcee1
-- title:
--   Mazur's principle at p for J₀(N₀p)
-- statement:
--   Let $N_0$ and $p$ be natural numbers, $N_0\neq 0$, with $p$ prime, $p\neq 0$, $p\neq 2$ and $p\nmid N_0$. Assume the Hecke input predicate `HeckeInputsAll` at both levels $N_0p$ and $N_0$, i.e. `HeckeInputsAlong` over $\overline{\mathbb Q}$ holds at every prime $\ell$, and that at each of the two levels the divisorial Hecke operators `heckeOperatorBar` commute pairwise. Let $W$ be a Weierstrass curve over $\mathbb Z$ with $\Delta_W\neq 0$, semistable at $p$ in the sense that $p\mid\Delta_W$ implies $p\nmid c_4(W)$, with $p$-torsion representation irreducible, meaning that the $p$-torsion of the points of $W_{\mathbb Q}$ over $\overline{\mathbb Q}$ is nontrivial and its only Galois-stable $\mathbb Z/p$-submodules are $0$ and the whole; and peu ramifiée at $p$, i.e. $p\mid v_p(\Delta_{W_{\mathbb Q}})$. Let $S$ be a finite set of primes consisting exactly of the primes dividing $N_0\,p\,|\Delta_W|$. Let $\mathfrak m$ be a maximal ideal of the polynomial Hecke algebra $\mathbb T=\mathbb Z[X_\ell:\ell\text{ prime}]$ containing the image of $p$ and containing $X_\ell-a_\ell(W)$ for every prime $\ell\notin S$, where $a_\ell(W)$ is the trace of Frobenius $\ell+1-\#W(\mathbb F_\ell)$ of the reduction of $W$ mod $\ell$. Assume finally that, for the `heckeModuleBar` action at level $N_0p$, the $\mathfrak m$-torsion submodule of $J_0(N_0p)=\mathrm{Pic}^0$ of the base change to $\overline{\mathbb Q}$ of the modular function field of level $N_0p$ is nonzero. Then `HasLowerLevelTorsion` holds for $S$, $\mathfrak m$ and $J_0(N_0)$ with its `heckeModuleBar` action: there is a $y\neq 0$ in $J_0(N_0)$ with $n\cdot y=0$ for every natural number $n$ whose image lies in $\mathfrak m$, and $(X_\ell-b)\cdot y=0$ for every prime $\ell\notin S$ and every integer $b$ with $X_\ell-b\in\mathfrak m$.
--
--   This is Mazur's principle in the form used for level lowering at $p$ (Ribet, Invent. Math. 100 (1990), Theorem 1.1, in the case $p\parallel N$): an irreducible mod $p$ eigensystem attached to $W$ which occurs in the Jacobian at level $N_0p$ and is finite at $p$ already occurs in the $\mathfrak m$-torsion at level $N_0$. It feeds the residual modularity step [`WeierstrassCurve.isResiduallyModularOfLevel_div_of_isPeuRamifieeAt`](thm.html#WeierstrassCurve.isResiduallyModularOfLevel_div_of_isPeuRamifieeAt), which removes the factor $p$ from the level.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_hasLowerLevelTorsion_jZero_of_isPeuRamifieeAt.lean

import Mathlib
import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_ModularCurve_HeckeInputsAll
import Definitions.Def_ModularCurve_MazurPrincipleCore
import Definitions.Def_FLTPrelim_ModularRep
import Definitions.Def_WeierstrassCurve_PeuRamifiee

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularCurve.hasLowerLevelTorsion_jZero_of_isPeuRamifieeAt
    (N₀ p : ℕ) [NeZero N₀] [Fact p.Prime] [NeZero p] (hp2 : p ≠ 2) (hpN₀ : ¬ p ∣ N₀)
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
