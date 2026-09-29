-- Prove2me | Theorems.Thm_ModularCurve_exists_pos_tateGenOpH_dia_pow_eq_one
-- name    : ModularCurve.exists_pos_tateGenOpH_dia_pow_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:51.361078+00:00
-- url     : https://prove2.me/theorems/1bbd9cb0-0b1e-5f03-8766-c42cb37690fd
-- title:
--   Diamond operators have finite order on the Tate module
-- statement:
--   Fix a natural number $N$ with $N \neq 0$, a prime $p$, a subgroup $H \le (\mathbb{Z}/N)^\times$, a set $S$ of natural numbers, and a unit $d \in (\mathbb{Z}/N)^\times$. Consider the generator `.dia d` of the indexing type [`CohCarrier.Gen N S`](def/CohCarrier_Inst.html#L13) of Hecke-type operators; the associated operator [`ModularCurve.genOpH N H S (.dia d)`](def/ModularCurve_XHOperators.html#L80) is by definition the additive endomorphism [`ModularCurve.diamondHBar N H d`](def/ModularCurve_XHOperators.html#L57) of the Jacobian group [`ModularCurve.JH N H`](def/ModularCurve_XH.html#L127), and [`ModularCurve.tateGenOpH N H S p (.dia d)`](def/ModularCurve_XHOperators.html#L99) is its image under [`ModularCurve.JH.tateEnd N H p`](def/ModularCurve_XH.html#L158), i.e. the induced $\mathbb{Z}_p$-linear endomorphism of [`TateModule p (ModularCurve.JH N H)`](def/EllipticCurve_TateModule.html#L15), the additive group of sequences $x : \mathbb{N} \to$ `JH N H` satisfying $p^n \cdot x_n = 0$ and $p \cdot x_{n+1} = x_n$ for all $n$. The assertion is that this endomorphism has finite multiplicative order: there exists $m \in \mathbb{N}$ with $0 < m$ and $(\mathrm{tateGenOpH}\, N\, H\, S\, p\, (\mathrm{dia}\, d))^m = 1$ in the ring of $\mathbb{Z}_p$-linear endomorphisms of the Tate module. The set $S$ enters only as an index of the generator type and plays no mathematical role here.
--
--   This records that the diamond operator $\langle d \rangle$ acts with finite order on the $p$-adic Tate module of $J_H(N)$, the group $(\mathbb{Z}/N)^\times$ being finite. It serves as the finite-order input in the analysis of joint eigenvectors for the pair $(T_\ell, \langle d \rangle)$, and is cited by [`ModularCurve.sq_ne_add_one_sq_mul_of_joint_eigenvector_tateGenOpH_T_dia`](thm.html#ModularCurve.sq_ne_add_one_sq_mul_of_joint_eigenvector_tateGenOpH_T_dia).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_pos_tateGenOpH_dia_pow_eq_one.lean

import Mathlib
import Definitions.Def_ModularCurve_XHOperators
import Definitions.Def_EllipticCurve_TateModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ModularCurve.exists_pos_tateGenOpH_dia_pow_eq_one
    (N p : ℕ) [NeZero N] [Fact p.Prime] (H : Subgroup (ZMod N)ˣ) (S : Set ℕ) (d : (ZMod N)ˣ) :
    ∃ m : ℕ, 0 < m ∧ (ModularCurve.tateGenOpH N H S p (.dia d)) ^ m = 1 := by sorry
