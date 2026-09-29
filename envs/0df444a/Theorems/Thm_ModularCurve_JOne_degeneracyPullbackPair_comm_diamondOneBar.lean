-- Prove2me | Theorems.Thm_ModularCurve_JOne_degeneracyPullbackPair_comm_diamondOneBar
-- name    : ModularCurve.JOne.degeneracyPullbackPair_comm_diamondOneBar
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.860483+00:00
-- url     : https://prove2.me/theorems/f4812b15-88d4-5efe-8c60-5f9690c74e3c
-- title:
--   Degeneracy pull-backs commute with ⟨ d⟩ for ℓ∤ d
-- statement:
--   Fix $N\ge 1$ and a prime $\ell\ge 1$ (both carrying `NeZero`), with $\ell\nmid N$, and put $N'=N\ell$. Assume [`ModularCurve.HeckeDiamondInputsAll`](def/ModularCurve_X1HeckeModule.html#L58) at both levels $N$ and $N'$: at each level $M\in\{N,N'\}$ this says that `HeckeInputsOneAlong` holds over $\overline{\mathbb{Q}}$ for $M$ and every prime, and that for every $d$ coprime to $M$ there is a $\mathbb{Q}$-algebra automorphism of the function field `x1FunctionField M` satisfying `IsDiamondAut M d`, together with an $\overline{\mathbb{Q}}$-algebra automorphism of `x1FunctionFieldBar M` which is a base change (in the sense of `IsBaseChangeAutOf`) of `diamondAut M d`. Let $i\in\{0,1\}$ and let $x$ be a point of `JOne N`, the degree-zero divisor class group $\mathrm{Pic}^0$ of `x1FunctionFieldBar N` over $\overline{\mathbb{Q}}$. The conclusion is that for every natural number $d$ with $\ell\nmid d$ (coprimality of $d$ with $N$ is not required), the $i$-th component of `degeneracyPullbackPair N N' ℓ` commutes with the diamond endomorphisms: its value at `diamondOneBar N d x` equals `diamondOneBar N' d` applied to its value at $x$. Here the $0$-th component is the $\mathrm{Pic}^0$ pull-back along the level inclusion `x1LevelInclBar` and the $1$-st along `x1LevelSubstBar` (the $\ell$-substitution `heckeBetaOneBar` followed by a level inclusion), both taken to be the zero homomorphism unless `DegeneracyPullbackInputs N N' ℓ` holds, and `diamondOneBar M d` is the $\mathbb{Z}$-linear endomorphism of `JOne M` induced by the action of the semilinear automorphism attached to `diamondAutBar M d`.
--
--   This is the compatibility of the two degeneracy pull-backs $J_1(N)\to J_1(N\ell)$, coming from $\tau\mapsto\tau$ and $\tau\mapsto\ell\tau$, with the diamond operators $\langle d\rangle$ for $d$ prime to $\ell$. It is the diamond half of the Hecke-equivariance statement [`ModularCurve.JOne.degeneracyPullbackPair_comm_heckeOperatorOneBar_diamondOneBar`](thm.html#ModularCurve.JOne.degeneracyPullbackPair_comm_heckeOperatorOneBar_diamondOneBar), which is what makes the degeneracy maps morphisms of Hecke modules away from $\ell$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JOne_degeneracyPullbackPair_comm_diamondOneBar.lean

import Mathlib
import Definitions.Def_ModularCurve_X1HeckeModule
import Definitions.Def_ModularCurve_X1DegeneracyPullback

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ModularCurve.JOne.degeneracyPullbackPair_comm_diamondOneBar
    (N : ℕ) [NeZero N] (ℓ : ℕ) [NeZero ℓ] (hℓ : ℓ.Prime) (hℓN : ¬ ℓ ∣ N)
    (N' : ℕ) (hN' : N' = N * ℓ)
    (hin : ModularCurve.HeckeDiamondInputsAll N) (hin' : ModularCurve.HeckeDiamondInputsAll N')
    (i : Fin 2) (x : ModularCurve.JOne N) :
    ∀ d : ℕ, ¬ ℓ ∣ d →
      ModularCurve.JOne.degeneracyPullbackPair N N' ℓ i (ModularCurve.diamondOneBar N d x) =
        ModularCurve.diamondOneBar N' d (ModularCurve.JOne.degeneracyPullbackPair N N' ℓ i x) := by sorry
