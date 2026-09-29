-- Prove2me | Theorems.Thm_ModularCurve_pair_heckeOperatorBar_eq_pair_fricke_heckeOperatorBar
-- name    : ModularCurve.pair_heckeOperatorBar_eq_pair_fricke_heckeOperatorBar
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.985053+00:00
-- url     : https://prove2.me/theorems/dfdd4449-43d6-5996-8b34-2eae51f92525
-- title:
--   Hecke operators and the Fricke-twisted Weil pairing on J₀(N)
-- statement:
--   Fix a nonzero natural number $N$, a prime $\ell$, a nonzero natural number $n$, and assume that both of the fields $\mathrm{modularFunctionFieldBar}\,N$ and $\mathrm{modularFunctionFieldBar}\,(N\ell)$ over $K=\overline{\mathbb{Q}}$ have principal divisors, i.e. every nonzero function has a degree-zero divisor recording its orders at all places. Let $e$ be a divisorial Weil pairing datum for $K$, $F=\mathrm{modularFunctionFieldBar}\,N$ and $n$: a $K$-valued pairing `e.pair` on the $n$-torsion of $\mathrm{Pic}^0$ (degree-zero divisors modulo principal ones) which agrees with the pairing attached to every Weil datum and whose classes can be moved to degree-zero divisors supported at rational places avoiding any prescribed finite set of places. Let $\sigma$ be a $K$-algebra automorphism of $F$ such that for all nonzero $a,b$ with $ab=N$, any element of $F$ whose underlying Laurent series is the coefficient base change of $\mathrm{qExpand}\,a\,(j)$ is sent by $\sigma$ to an element with Laurent series the base change of $\mathrm{qExpand}\,b\,(j)$. Let $x,y,Tx,wy,wTy$ be $n$-torsion classes in $\mathrm{Pic}^0$ with $Tx=T_\ell x$, $wy=\sigma\cdot y$ and $wTy=\sigma\cdot(T_\ell y)$ in $\mathrm{JZero}\,N$, where $T_\ell=\mathrm{heckeOperatorBar}\,N\,\ell$ and $\sigma$ acts through the semilinear automorphism `ofAlgAut σ`. Then $e.\mathrm{pair}\,Tx\,wy=e.\mathrm{pair}\,x\,wTy$.
--
--   This is the self-adjointness of the Hecke operator $T_\ell$ for the Weil pairing twisted by the Fricke involution $w_N$, i.e. $e(T_\ell x, w_N y)=e(x, w_N T_\ell y)$, expressed for classes named by hypotheses rather than by applying the operators inside the pairing. It is used in the construction of Galois- and Hecke-compatible pairings on the $n$-torsion of $J_0(N)$ and in the determination of Frobenius determinants on bases of the rational Tate module of $J_0(N)$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_pair_heckeOperatorBar_eq_pair_fricke_heckeOperatorBar.lean

import Mathlib
import Definitions.Def_ModularCurve_HeckeModule
import Definitions.Def_AlgebraicCurve_FunctionFieldWeilPairingDivisorial

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularCurve.pair_heckeOperatorBar_eq_pair_fricke_heckeOperatorBar
    (N : ℕ) [NeZero N] (ℓ : Nat.Primes) (n : ℕ) [NeZero n]
    [AlgebraicCurve.HasPrincipalDivisors (AlgebraicClosure ℚ) (ModularCurve.modularFunctionFieldBar N)]
    [AlgebraicCurve.HasPrincipalDivisors (AlgebraicClosure ℚ) (ModularCurve.modularFunctionFieldBar (N * ℓ))]
    (e : AlgebraicCurve.DivisorialWeilPairingData (AlgebraicClosure ℚ) (ModularCurve.modularFunctionFieldBar N) n)
    (σ : ModularCurve.modularFunctionFieldBar N ≃ₐ[AlgebraicClosure ℚ] ModularCurve.modularFunctionFieldBar N)
    (hσ : ∀ (a b : ℕ) [NeZero a] [NeZero b], a * b = N →
      ∀ x : ModularCurve.modularFunctionFieldBar N,
        (x : LaurentSeries (AlgebraicClosure ℚ))
            = ModularCurve.coeffEmb (AlgebraicClosure ℚ) (ModularCurve.qExpand ℚ a ModularCurve.jq) →
          ((σ x : ModularCurve.modularFunctionFieldBar N) : LaurentSeries (AlgebraicClosure ℚ))
            = ModularCurve.coeffEmb (AlgebraicClosure ℚ) (ModularCurve.qExpand ℚ b ModularCurve.jq))
    (x y Tx wy wTy : AlgebraicCurve.Pic0.torsion (AlgebraicClosure ℚ) (ModularCurve.modularFunctionFieldBar N) n)
    (hTx : (Tx : ModularCurve.JZero N) = ModularCurve.heckeOperatorBar N ℓ (x : ModularCurve.JZero N))
    (hwy : (wy : ModularCurve.JZero N) = AlgebraicCurve.SemilinearAut.ofAlgAut σ • (y : ModularCurve.JZero N))
    (hwTy : (wTy : ModularCurve.JZero N)
      = AlgebraicCurve.SemilinearAut.ofAlgAut σ • ModularCurve.heckeOperatorBar N ℓ (y : ModularCurve.JZero N)) :
    e.pair Tx wy = e.pair x wTy := by sorry
