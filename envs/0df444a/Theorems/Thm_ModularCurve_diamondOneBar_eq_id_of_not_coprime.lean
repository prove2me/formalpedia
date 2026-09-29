-- Prove2me | Theorems.Thm_ModularCurve_diamondOneBar_eq_id_of_not_coprime
-- name    : ModularCurve.diamondOneBar_eq_id_of_not_coprime
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:49.889759+00:00
-- url     : https://prove2.me/theorems/163e23be-8b63-53d8-be7a-87b73a085de6
-- title:
--   Diamond operator on J₁(M) is trivial for d not coprime to M
-- statement:
--   Let $M$ be a nonzero natural number and let $d$ be a natural number with $\gcd(d,M)\neq 1$, i.e. $d$ and $M$ are not coprime. Write $J_1(M)$ for `JOne M`, the degree-zero Picard group $\mathrm{Pic}^0$ of the function field `x1FunctionFieldBar M` of $X_1(M)$ over $\overline{\mathbb Q}$, viewed as a $\mathbb Z$-module. The operator `diamondOneBar M d` is the $\mathbb Z$-linear endomorphism of $J_1(M)$ given by the action on $\mathrm{Pic}^0$ of the semilinear automorphism attached to the $\overline{\mathbb Q}$-algebra automorphism `diamondAutBar M d`, namely the pair consisting of that automorphism of `x1FunctionFieldBar M` together with the identity on $\overline{\mathbb Q}$ (the image of `diamondAutBar M d` under the monoid homomorphism `SemilinearAut.ofAlgAut`, acting distributively on $\mathrm{Pic}^0$); here `diamondAutBar M d` is the base change to $\overline{\mathbb Q}$ of the diamond automorphism `diamondAut M d` of the function field of $X_1(M)$. The assertion is that under the hypothesis $\neg\,\mathrm{Coprime}(d,M)$ this endomorphism is the identity map of $J_1(M)$.
--
--   This records the degenerate case of the diamond operators $\langle d\rangle$ acting on the Jacobian of $X_1(M)$: the project's diamond operators are defined for every natural number $d$, and for $d$ not prime to the level the defining construction returns the trivial automorphism, so the induced operator on $\mathrm{Pic}^0$ is the identity rather than being undefined. It is used in the bookkeeping for the Hecke–diamond action on $J_1(M)$, for instance in the statements relating Hecke and Galois operators to the Abel–Jacobi map and to the Tate module of $J_1(M)$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_diamondOneBar_eq_id_of_not_coprime.lean

import Mathlib
import Definitions.Def_ModularCurve_X1Diamond

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ModularCurve.diamondOneBar_eq_id_of_not_coprime
    (M : ℕ) [NeZero M] {d : ℕ} (h : ¬ Nat.Coprime d M) :
    ModularCurve.diamondOneBar M d = LinearMap.id := by sorry
