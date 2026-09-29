-- Prove2me | Theorems.Thm_ModularCurve_card_projectiveLine_zmod
-- name    : ModularCurve.card_projectiveLine_zmod
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:49.598281+00:00
-- url     : https://prove2.me/theorems/da9cf975-16fa-5474-94c2-d46f76a0f8b3
-- title:
--   #P¹(ℤ/N)=ψ(N)
-- statement:
--   Let $N$ be a natural number with $N \neq 0$. The projective line `ProjectiveLine (ZMod N)` over the ring $\mathbb{Z}/N\mathbb{Z}$ is, by definition, the quotient of the unimodular rows over that ring by the equivalence relation `unimodularRowSetoid`. The assertion is that the cardinality of this quotient, measured by `Nat.card`, equals $\psi(N)$, where `dedekindPsi N` is defined as the sum $\sum_{d \mid N,\ d \text{ squarefree}} N/d$ over the squarefree divisors $d$ of $N$ (so $\psi(1)=1$, and in general $\psi(N)=N\prod_{p \mid N}(1+p^{-1})$). Since this value is a positive natural number, the statement in particular contains the finiteness of $\mathbb{P}^1(\mathbb{Z}/N\mathbb{Z})$, `Nat.card` being $0$ for infinite types. The proof cites the multiplicativity of $\psi$ on coprime arguments, [`ModularCurve.dedekindPsi_mul_of_coprime`](thm.html#ModularCurve.dedekindPsi_mul_of_coprime), and its value $\psi(p^k) = p^k + p^{k-1}$ at prime powers with $k \neq 0$, [`ModularCurve.dedekindPsi_prime_pow`](thm.html#ModularCurve.dedekindPsi_prime_pow).
--
--   This is the classical count of the points of the projective line over $\mathbb{Z}/N\mathbb{Z}$ by the Dedekind psi function. It feeds the index formula $[\mathrm{SL}_2(\mathbb{Z}) : \Gamma_0(N)] = \psi(N)$ in [`ModularCurve.Gamma0_index`](thm.html#ModularCurve.Gamma0_index) and the companion counting statement [`ZMod.natCard_isAddCyclic_addSubgroup_prod_eq_dedekindPsi`](thm.html#ZMod.natCard_isAddCyclic_addSubgroup_prod_eq_dedekindPsi).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_card_projectiveLine_zmod.lean

import Definitions.Def_ModularCurve_ProjectiveLine
import Definitions.Def_ModularCurve_X0

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve

theorem ModularCurve.card_projectiveLine_zmod (N : ℕ) (hN : N ≠ 0) : Nat.card (ProjectiveLine (ZMod N)) = dedekindPsi N := by sorry
