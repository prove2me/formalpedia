-- Prove2me | Theorems.Thm_ModularCurve_LevelRelabelling_exists_mem_Gamma_relabel_eq_of_weilPairing0_eq
-- name    : ModularCurve.LevelRelabelling.exists_mem_Gamma_relabel_eq_of_weilPairing0_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:42.499921+00:00
-- url     : https://prove2.me/theorems/80ac7403-ad45-5dc2-b6d9-ff25c0872371
-- title:
--   Transitivity of Γ(N₀) on Weil-normalised level-ℓ structures
-- statement:
--   Let $K$ be an algebraically closed field, $W$ a Weierstrass curve over $K$ that is elliptic, and $\ell$ a prime with $3 \le \ell$ and $\ell \ne 0$ in $K$. Let $D = (x_P, y_P, x_Q, y_Q)$ and $D' = (x_{P'}, y_{P'}, x_{Q'}, y_{Q'})$ be two quadruples of elements of $K$, each a level-$\ell$ structure for $W$ in the sense of [`ModularCurve.IsLevelPStructure`](def/ModularCurve_KatzLevelP.html#L104): both coordinate pairs satisfy the affine Weierstrass equation of $W$, the polynomial $W.\mathrm{pre}\Psi\,\ell$ vanishes at the two $x$-coordinates, and both $\mathrm{indepElt}\,W\,\ell\,x_P\,x_Q = \prod_{a=1}^{(\ell-1)/2}\bigl(x_Q\,(W.\Psi\mathrm{Sq}\,a)(x_P) - (W.\Phi\,a)(x_P)\bigr)$ and the same expression with the roles of $x_P$ and $x_Q$ exchanged are units. Assume further that the two structures have the same Weil pairing value: $\mathrm{weilPairing0}$ of $W$ over $K$ at index $\ell$, evaluated on the points of the base change of $W$ to $K$ attached to $(x_P,y_P)$ and $(x_Q,y_Q)$ (each pair being read as the corresponding affine point when it is nonsingular, and as the point at infinity otherwise), agrees with its value on the two points attached to $D'$. Finally let $N_0$ be a nonzero natural number coprime to $\ell$. Then there is $\gamma \in \mathrm{SL}_2(\mathbb{Z})$ lying in the principal congruence subgroup $\Gamma(N_0)$ such that $D'$ is the relabelling of $D$ by $\gamma$: writing $P$ and $Q$ for the points attached to $D$, the quadruple $D'$ consists of the coordinates of $\gamma_{00}P + \gamma_{10}Q$ followed by those of $\gamma_{01}P + \gamma_{11}Q$, coordinates of the point at infinity being taken to be $(0,0)$.
--
--   This is the transitivity statement underlying the comparison of Katz-style level-$\ell$ structures: $\mathrm{SL}_2(\mathbb{Z})$ acts transitively on ordered $\ell$-division bases with a prescribed Weil pairing value, and the relabelling matrix may moreover be chosen congruent to the identity modulo any auxiliary modulus $N_0$ prime to $\ell$. It is used in the counting of level-$\ell$ structures with fixed pairing value and in the analysis of level automorphisms and maximal points on full-level modular curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_LevelRelabelling_exists_mem_Gamma_relabel_eq_of_weilPairing0_eq.lean

import Mathlib
import Definitions.Def_ModularCurve_KatzLevelP
import Definitions.Def_ModularCurve_LevelRelabelling
import Definitions.Def_EllipticCurve_WeilPairingFun

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open ModularCurve ModularCurve.LevelRelabelling WeierstrassCurve.Affine
open scoped MatrixGroups

theorem ModularCurve.LevelRelabelling.exists_mem_Gamma_relabel_eq_of_weilPairing0_eq
    {K : Type u} [Field K] [IsAlgClosed K] [DecidableEq K]
    (W : WeierstrassCurve K) [W.IsElliptic]
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ3 : 3 ≤ ℓ) (hℓK : (ℓ : K) ≠ 0)
    (D D' : ModularCurve.LevelPData K)
    (hD : ModularCurve.IsLevelPStructure W ℓ D) (hD' : ModularCurve.IsLevelPStructure W ℓ D')

    (hpin : weilPairing0 W K (ℓ : ℤ) (toPoint (W.baseChange K) D.xP D.yP) (toPoint (W.baseChange K) D.xQ D.yQ) =
      weilPairing0 W K (ℓ : ℤ) (toPoint (W.baseChange K) D'.xP D'.yP) (toPoint (W.baseChange K) D'.xQ D'.yQ))
    (N₀ : ℕ) [NeZero N₀] (hN₀ : Nat.Coprime N₀ ℓ) :
    ∃ γ : SL(2, ℤ), γ ∈ CongruenceSubgroup.Gamma N₀ ∧
      D' = LevelPData.relabel W ((γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) : Matrix (Fin 2) (Fin 2) ℤ) D := by sorry
