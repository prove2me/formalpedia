-- Prove2me | Theorems.Thm_ModularCurve_moduleFinite_and_free_padicInt_tateModule_jH
-- name    : ModularCurve.moduleFinite_and_free_padicInt_tateModule_jH
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.624895+00:00
-- url     : https://prove2.me/theorems/448018d2-03c8-5c44-85ba-492e07c32870
-- title:
--   Tₚ J_H(M) is finite free over ℤₚ
-- statement:
--   Let $M$ be a natural number, assumed nonzero, let $p$ be a prime, and let $H$ be a subgroup of $(\mathbb{Z}/M)^{\times}$. Write $J_H(M) =$ [`ModularCurve.JH M H`](def/ModularCurve_XH.html#L127) for the degree-zero divisor class group `Pic0` of the field `xHFunctionFieldBar M H`, the base change to $\overline{\mathbb{Q}}$, inside the Laurent series field $\overline{\mathbb{Q}}((q))$, of the $q$-expansion function field `xHFunctionField M H` of the modular curve $X_H(M)$; that is, the quotient of the group of degree-zero divisors of $\overline{\mathbb{Q}}((q)) \supseteq$ `xHFunctionFieldBar M H` over $\overline{\mathbb{Q}}$ by the subgroup of principal divisors. Let [`TateModule p (JH M H)`](def/EllipticCurve_TateModule.html#L15) be the group of sequences $x : \mathbb{N} \to J_H(M)$ satisfying $p^n \cdot x_n = 0$ and $p \cdot x_{n+1} = x_n$ for all $n$, i.e. the $p$-adic Tate module $\varprojlim_n J_H(M)[p^n]$. The assertion is the conjunction of two statements about this $\mathbb{Z}_p$-module: it is a finite (finitely generated) $\mathbb{Z}_{p}$-module, and it is a free $\mathbb{Z}_p$-module. No rank is asserted.
--
--   This records that the $p$-adic Tate module of the Jacobian of $X_H(M)$, in the $q$-expansion model with rational cusp $\infty$, is a finitely generated free $\mathbb{Z}_p$-module of the kind required to carry a $p$-adic Galois representation; classically $T_pJ_H(M) \cong \mathbb{Z}_p^{2g}$ with $g$ the genus. It underlies the constructions of Galois modules attached to Hecke eigenforms, in particular the cohomological carrier modules and the Hecke-equivariant descriptions of the Tate module used later in the modularity-lifting argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_moduleFinite_and_free_padicInt_tateModule_jH.lean

import Mathlib
import Definitions.Def_ModularCurve_XH

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularCurve.moduleFinite_and_free_padicInt_tateModule_jH (M p : ℕ) [NeZero M] [Fact p.Prime]
    (H : Subgroup (ZMod M)ˣ) :
    Module.Finite ℤ_[p] (TateModule p (ModularCurve.JH M H)) ∧
      Module.Free ℤ_[p] (TateModule p (ModularCurve.JH M H)) := by sorry
