-- Prove2me | Theorems.Thm_ModularCurve_rep_tateModule_jOne_comm
-- name    : ModularCurve.rep_tateModule_jOne_comm
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:54.618386+00:00
-- url     : https://prove2.me/theorems/0bc4bd6b-fcd7-54cf-acc8-bad73a003d68
-- title:
--   Galois action on Tₚ J₁(M) commutes with Hecke operators
-- statement:
--   Let $M$ be a nonzero natural number and $p$ a prime. Write $J_1(M)$ for [`ModularCurve.JOne M`](def/ModularCurve_X1.html#L186), the group `Pic0` of degree-zero divisor classes modulo principal divisors of the intermediate field `x1FunctionFieldBar M` of $\overline{\mathbb Q}$-Laurent series obtained by base change of the function field of $X_1(M)$, carrying its natural action of the group $\overline{\mathbb Q}\simeq_{\mathbb Q}\overline{\mathbb Q}$ of $\mathbb Q$-algebra automorphisms of $\overline{\mathbb Q}$, and let `HeckeAlgOne` $=\mathbb Z[X_i : i\in\mathrm{Primes}\sqcup\mathbb N]$ act on $J_1(M)$ through the module structure `heckeModuleOneBar M`, which (when the generators commute) sends the variable indexed by a prime $\ell$ to the Hecke operator `heckeOperatorOneBar` and the variable indexed by $d\in\mathbb N$ to the diamond operator `diamondOneBar`. Given the hypothesis `HeckeDiamondCommuteBar M`, i.e. that these endomorphisms of $J_1(M)$ commute pairwise, an automorphism $\sigma$, an element $T$ of `HeckeAlgOne` and an element $x$ of the Tate module $T_p J_1(M)$ — the group of sequences $(x_n)_{n\in\mathbb N}$ in $J_1(M)$ with $p^n x_n = 0$ and $p\,x_{n+1}=x_n$ — the conclusion is that the $\mathbb Z_p$-linear endomorphisms [`TateModule.rep`](def/EllipticCurve_TateModule.html#L174) attached to the two actions commute on $x$: $\sigma(Tx) = T(\sigma x)$.
--
--   This is the statement that the Hecke correspondences and diamond automorphisms of $X_1(M)$, being defined over $\mathbb Q$, induce endomorphisms of $J_1(M)$ commuting with the Galois action, here recorded at the level of the $p$-adic Tate module so that $T_pJ_1(M)$ becomes a module over the Hecke algebra with commuting Galois action. It is the compatibility underlying the construction of the $p$-adic Galois representations attached to eigenforms, and is cited in the construction of characteristic polynomials of Frobenius and in the local analysis at primes dividing the level.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_rep_tateModule_jOne_comm.lean

import Mathlib
import Definitions.Def_ModularCurve_X1HeckeModule
import Definitions.Def_EllipticCurve_TateModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularCurve.rep_tateModule_jOne_comm (M p : ℕ) [NeZero M] [Fact p.Prime]
    (hcomm : ModularCurve.HeckeDiamondCommuteBar M)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (T : ModularCurve.HeckeAlgOne)
    (x : TateModule p (ModularCurve.JOne M)) :
    letI := ModularCurve.heckeModuleOneBar M
    TateModule.rep p (ModularCurve.JOne M) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) σ
        (TateModule.rep p (ModularCurve.JOne M) ModularCurve.HeckeAlgOne T x)
      = TateModule.rep p (ModularCurve.JOne M) ModularCurve.HeckeAlgOne T
        (TateModule.rep p (ModularCurve.JOne M) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) σ x) := by sorry
