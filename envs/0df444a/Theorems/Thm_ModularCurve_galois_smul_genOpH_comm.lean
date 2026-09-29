-- Prove2me | Theorems.Thm_ModularCurve_galois_smul_genOpH_comm
-- name    : ModularCurve.galois_smul_genOpH_comm
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.414366+00:00
-- url     : https://prove2.me/theorems/014c3ec0-1e77-5d53-abba-8007f9735238
-- title:
--   Galois action commutes with Hecke and diamond operators on J_H
-- statement:
--   Let $M$ be a nonzero natural number, $H$ a subgroup of $(\mathbb{Z}/M)^\times$ and $S$ a set of natural numbers. Let $\sigma$ be a $\mathbb{Q}$-algebra automorphism of $\overline{\mathbb{Q}}$ (the chosen algebraic closure `AlgebraicClosure ℚ`), let $g$ be an element of [`CohCarrier.Gen M S`](def/CohCarrier_Inst.html#L13) — that is, one of the formal symbols $T_\ell$ for a prime $\ell\notin S$ with $\ell\nmid M$, $U_q$ for a prime $q\mid M$, or $\langle d\rangle$ for a unit $d\in(\mathbb{Z}/M)^\times$ — and let $P$ be an element of $J_H(M)=$ [`ModularCurve.JH M H`](def/ModularCurve_XH.html#L127), the group $\mathrm{Pic}^0$ of the field $\overline{\mathbb{Q}}\cdot F$ over $\overline{\mathbb{Q}}$, where $F=$ `xHFunctionField M H` sits in $\mathbb{Q}((q))$ and the compositum is taken inside $\overline{\mathbb{Q}}((q))$; thus $J_H(M)$ is the group of degree-zero divisors modulo principal divisors. Then the additive endomorphism `genOpH M H S g` of $J_H(M)$ attached to $g$ — the Hecke operator `heckeOperatorHAlong` at $\ell$ respectively $q$ in the two prime cases, and the endomorphism induced by the automorphism `diamondAutHBar M H d` in the third — commutes with the Galois action: $\sigma\cdot(g\,P)=g\,(\sigma\cdot P)$, where $\sigma$ acts on $J_H(M)$ through its coefficientwise action on Laurent series.
--
--   This is the statement that the Hecke correspondences $T_\ell$, $U_q$ and the diamond operators $\langle d\rangle$ on the Jacobian of $X_H(M)$ are defined over $\mathbb{Q}$, so that $J_H(M)(\overline{\mathbb{Q}})$ is a module over the Hecke algebra compatibly with its $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$-action. It is what makes the torsion of $J_H(M)$ a Galois–Hecke module, and it is used in the construction of the Galois representations attached to Hecke eigenclasses and of the lattices carrying them.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_galois_smul_genOpH_comm.lean

import Mathlib
import Definitions.Def_ModularCurve_XHOperators

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularCurve.galois_smul_genOpH_comm (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) (S : Set ℕ)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (g : CohCarrier.Gen M S)
    (P : ModularCurve.JH M H) :
    σ • (ModularCurve.genOpH M H S g P) = ModularCurve.genOpH M H S g (σ • P) := by sorry
