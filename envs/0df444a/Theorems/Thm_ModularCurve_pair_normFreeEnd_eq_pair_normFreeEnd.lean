-- Prove2me | Theorems.Thm_ModularCurve_pair_normFreeEnd_eq_pair_normFreeEnd
-- name    : ModularCurve.pair_normFreeEnd_eq_pair_normFreeEnd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.985053+00:00
-- url     : https://prove2.me/theorems/c87e2b1c-9564-5d00-8dd4-711ee6fabd7e
-- title:
--   Self-adjointness of the norm-free endomorphism under the Weil pairing
-- statement:
--   Fix natural numbers $M \neq 0$ and $q$ with $q \mid M$, and assume that the extension $\overline{\mathbb Q} \subseteq \overline{\mathbb Q}\cdot F(\Gamma_1(M))$ — the field [`ModularCurve.x1FunctionFieldBar M`](def/ModularCurve_X1.html#L182), obtained by base change to $\overline{\mathbb Q}$ of the function field of $X_1(M)$ inside Laurent series — satisfies [`AlgebraicCurve.HasPrincipalDivisors`](def/AlgebraicCurve_DivisorClassGroup.html#L217), i.e. every nonzero element $f$ of it has a divisor: a finitely supported integer-valued function on places whose value at each place $v$ is $\operatorname{ord}_v(f)$ and whose degree is $0$. Let $n \neq 0$ be a natural number and let $e$ be a divisorial Weil pairing datum of order $n$ for this extension, that is, a function `pair` on pairs of $n$-torsion classes in $\operatorname{Pic}^0 =$ [`ModularCurve.JOne M`](def/ModularCurve_X1.html#L186) with values in $\overline{\mathbb Q}$, which agrees with the pairing attached to any Weil datum via its left and right classes, and which satisfies the moving property that every $n$-torsion class is represented by a degree-zero divisor supported at rational places avoiding any prescribed finite set of places. Write $N$ for the endomorphism [`ModularCurve.normFreeEnd M (ModularCurve.normFreeRepsAt M q)`](def/ModularCurve_X1PrimitiveSpecialization.html#L27) of $\operatorname{Pic}^0$, namely $x \mapsto |S|\,x - \sum_{d \in S} \langle d \rangle x$, where $S$ is the set of $d < M$ with $\gcd(d,M) = 1$ and $d \equiv 1 \pmod{M/q}$ and $\langle d \rangle$ denotes `diamondOneBar M d`. Let $x, y \in \operatorname{Pic}^0$ satisfy $n x = 0$, $n y = 0$, $n (N x) = 0$ and $n (N y) = 0$, so that $x$, $y$, $Nx$, $Ny$ are all $n$-torsion classes. Then $e(Nx, y) = e(x, Ny)$.
--
--   This is the statement that the norm-free endomorphism $N = |S| - \sum_{d \in S} \langle d \rangle$ of the Jacobian of $X_1(M)$ is self-adjoint for the Weil pairing, the underlying point being that the Rosati-type adjoint of a diamond operator is the diamond operator at the inverse residue and that $S$ represents a subgroup of $(\mathbb Z/M)^\times$. It is used in the analysis of the norm-free part of the Tate module, in [`ModularCurve.tateModule_eq_zero_of_forall_toPic0Pair_sp_eq_zero_of_ne_normFreePartAt_pinnedV3`](thm.html#ModularCurve.tateModule_eq_zero_of_forall_toPic0Pair_sp_eq_zero_of_ne_normFreePartAt_pinnedV3).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_pair_normFreeEnd_eq_pair_normFreeEnd.lean

import Mathlib
import Definitions.Def_ModularCurve_X1PrimitiveSpecializationAtP
import Definitions.Def_AlgebraicCurve_FunctionFieldWeilPairingDivisorial

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ModularCurve.pair_normFreeEnd_eq_pair_normFreeEnd
    (M q : ℕ) [NeZero M] (hqM : q ∣ M)
    [AlgebraicCurve.HasPrincipalDivisors (AlgebraicClosure ℚ) ↥(ModularCurve.x1FunctionFieldBar M)]
    {n : ℕ} [NeZero n]
    (e : AlgebraicCurve.DivisorialWeilPairingData (AlgebraicClosure ℚ) ↥(ModularCurve.x1FunctionFieldBar M) n)
    (x y : ModularCurve.JOne M) (hx : (n : ℤ) • x = 0) (hy : (n : ℤ) • y = 0)
    (hNx : (n : ℤ) • ModularCurve.normFreeEnd M (ModularCurve.normFreeRepsAt M q) x = 0)
    (hNy : (n : ℤ) • ModularCurve.normFreeEnd M (ModularCurve.normFreeRepsAt M q) y = 0) :
    e.pair ⟨ModularCurve.normFreeEnd M (ModularCurve.normFreeRepsAt M q) x, AlgebraicCurve.Pic0.mem_torsion.mpr hNx⟩
        ⟨y, AlgebraicCurve.Pic0.mem_torsion.mpr hy⟩ =
      e.pair ⟨x, AlgebraicCurve.Pic0.mem_torsion.mpr hx⟩
        ⟨ModularCurve.normFreeEnd M (ModularCurve.normFreeRepsAt M q) y, AlgebraicCurve.Pic0.mem_torsion.mpr hNy⟩ := by sorry
