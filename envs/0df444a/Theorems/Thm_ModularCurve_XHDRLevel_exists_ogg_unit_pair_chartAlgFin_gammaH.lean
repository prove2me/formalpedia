-- Prove2me | Theorems.Thm_ModularCurve_XHDRLevel_exists_ogg_unit_pair_chartAlgFin_gammaH
-- name    : ModularCurve.XHDRLevel.exists_ogg_unit_pair_chartAlgFin_gammaH
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.68297+00:00
-- url     : https://prove2.me/theorems/ce89b0cf-1f37-528b-accd-dd2f28f000c9
-- title:
--   Ogg's unit pair Δ(q)/Δ(qᵖ) in the j-finite chart ring
-- statement:
--   Let $p$ be a prime and $M$ a non-zero natural number with $p \mid M$ but $p^2 \nmid M$, and let $H$ be a subgroup of $(\mathbb{Z}/M)^\times$ containing every unit whose image under the reduction map `ZMod.unitsMap` to $(\mathbb{Z}/(M/p))^\times$ is trivial. Assume the Laurent series `jqModC ℚ`, namely $q^{-1}$ times the rational image of the integral power series `jNum` $= E_4^3 \cdot$ `dedekindEtaUnitInv`, lies in `qExpFunctionFieldC ℚ ⊤`, the subfield of $\mathbb{Q}((q))$ generated over $\mathbb{Q}$ by the quotients of $q$-expansions of pairs of modular forms of equal weight and full level having integral $q$-expansions. Write $F_M$ for `qExpFunctionFieldC ℚ (ΓM M H)` and $F_N$ for `qExpFunctionFieldC ℚ (ΓN p M H hpM)`, the corresponding fields for the groups `ΓM M H` and `ΓN p M H hpM`. Let $\sigma$ be a $\mathbb{Q}$-algebra automorphism of $F_M$ satisfying the Atkin–Lehner law: whenever $f \in F_M$ and $u \in F_N$ have the same underlying Laurent series, the Laurent series of $\sigma f$ is `qExpand ℚ p` of that of $u$, i.e. the substitution $q \mapsto q^p$ (multiplication by $p$ on exponents). Then there exist $v, w$ in the subalgebra `chartAlgFin p (ΓM M H) hj` of $F_M$ — the elements of $F_M$ integral over the subalgebra generated over the base ring `R p` by the element `jAt (ΓM M H) hj` — whose Laurent series are `modularUnitSeries p` $=$ `deltaSeries` $\cdot$ (`qExpand ℚ p deltaSeries`)$^{-1}$, that is $\Delta(q)/\Delta(q^p)$, and $p^{12} \cdot$ (`modularUnitSeries p`)$^{-1}$ respectively, such that $v w$ is the image of $(p)^{12} \in$ `R p` under the structure map, and $\sigma(v) = w$ in $F_M$.
--
--   This provides Ogg's modular unit $\Delta(q)/\Delta(q^p)$ together with its partner $p^{12}\Delta(q^p)/\Delta(q)$ inside the $j$-finite chart ring of the two-chart integral model of $X_H(M)$ over the local base `R p`, with the two exchanged by the Atkin–Lehner automorphism and with product the constant $p^{12}$. It feeds the analysis of the integral model of $X_H(M)$ at $p$, in particular the construction of retractions killing the relevant tensor element and the unramifiedness statements for the chart algebras.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XHDRLevel_exists_ogg_unit_pair_chartAlgFin_gammaH.lean

import Mathlib
import Definitions.Def_ModularCurve_XHDRModelAtP
import Definitions.Def_ModularCurve_ModularUnit
import Definitions.Def_ModularCurve_LaurentCoeff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicCurve ModularCurve ModularCurve.XHDRLevel
open scoped MatrixGroups TensorProduct

set_option maxHeartbeats 800000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem ModularCurve.XHDRLevel.exists_ogg_unit_pair_chartAlgFin_gammaH
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H)
    (hj : jqModC ℚ ∈ qExpFunctionFieldC ℚ (⊤ : Subgroup SL(2, ℤ)))
    (σ : ↥(qExpFunctionFieldC ℚ (ΓM M H)) ≃ₐ[ℚ] ↥(qExpFunctionFieldC ℚ (ΓM M H)))
    (hσ : haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
      ∀ (f : ↥(qExpFunctionFieldC ℚ (ΓM M H))) (u : ↥(qExpFunctionFieldC ℚ (ΓN p M H hpM))), (f : LaurentSeries ℚ) = (u : LaurentSeries ℚ) →
        ((σ f : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ) = qExpand ℚ p (u : LaurentSeries ℚ)) :
    ∃ v w : ↥(chartAlgFin p (ΓM M H) hj),
      (((v : ↥(chartAlgFin p (ΓM M H) hj)) : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ) = modularUnitSeries p ∧
      (((w : ↥(chartAlgFin p (ΓM M H) hj)) : ↥(qExpFunctionFieldC ℚ (ΓM M H))) : LaurentSeries ℚ) = (p : LaurentSeries ℚ) ^ 12 * (modularUnitSeries p)⁻¹ ∧
      v * w = algebraMap (R p) ↥(chartAlgFin p (ΓM M H) hj) (((p : ℕ) : R p) ^ 12) ∧
      σ ((v : ↥(chartAlgFin p (ΓM M H) hj)) : ↥(qExpFunctionFieldC ℚ (ΓM M H))) = ((w : ↥(chartAlgFin p (ΓM M H) hj)) : ↥(qExpFunctionFieldC ℚ (ΓM M H))) := by sorry
