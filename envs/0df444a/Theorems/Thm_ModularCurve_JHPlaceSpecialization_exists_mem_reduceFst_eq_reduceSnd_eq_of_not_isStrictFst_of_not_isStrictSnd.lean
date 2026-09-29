-- Prove2me | Theorems.Thm_ModularCurve_JHPlaceSpecialization_exists_mem_reduceFst_eq_reduceSnd_eq_of_not_isStrictFst_of_not_isStrictSnd
-- name    : ModularCurve.JHPlaceSpecialization.exists_mem_reduceFst_eq_reduceSnd_eq_of_not_isStrictFst_of_not_isStrictSnd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.315379+00:00
-- url     : https://prove2.me/theorems/56692576-6966-5b2d-9ea2-7d88b5c2cf9b
-- title:
--   Non-strict places lie over supersingular node pairs
-- statement:
--   Fix a prime $p$, a positive integer $M$ with $p \mid M$, a subgroup $H \le (\mathbb{Z}/M)^\times$, and a valuation subring $A$ of $\overline{\mathbb{Q}}$ with algebraically closed residue field $\kappa$ of characteristic $p$; further data are assumed: $p^2 \nmid M$, the condition that every unit of $\mathbb{Z}/M$ mapping to $1$ in $(\mathbb{Z}/(M/p))^\times$ lies in $H$, the hypothesis $(p) \in A.\mathrm{nonunits}$ expressing that $A$ lies over $p$, and an $\overline{\mathbb{Q}}$-algebra automorphism $\theta$ of $F_M := \overline{\mathbb{Q}}\cdot F(X_H(M))$ inside Laurent series. Let $\alpha,\beta$ be integral $\overline{\mathbb{Q}}$-algebra maps from $F_{M/p} := \overline{\mathbb{Q}}\cdot F(X_{H'}(M/p))$, $H'$ the image of $H$ in $(\mathbb{Z}/(M/p))^\times$, into $F_M$; let $\delta$ be a self-map of the set of places of $\bar F :=$ the $q$-expansion function field of $\Gamma_N(p,M,H)$ over $\kappa$, and write $\varphi$ for `qExpFrobeniusPlaceModL`. Let $SS$ be a finite set of pairs of such places whose members are exactly the pairs $(s_1,s_2)$ with $s_2$ a supersingular place and $s_1 = \varphi(s_2)$. Let $\mathrm{Psp}$ be a `JHPlaceSpecialization` packet for $(p,M,H,A)$, with specialization map $\mathrm{sp}$ on places of $F_{M/p}$, and put $\mathrm{red}_1(W) = \mathrm{sp}(W|_\alpha)$ and $\mathrm{red}_2(W) = \delta(\mathrm{sp}(W|_\beta))$. Assume the dichotomy that every place $W$ of $F_M$ satisfies $\mathrm{red}_1(W) = \varphi(\mathrm{red}_2(W))$ or $\delta(\varphi(\mathrm{red}_1(W))) = \mathrm{red}_2(W)$. Let $V$ be a place of $F_M$ over $\overline{\mathbb{Q}}$ which is strict of neither kind, i.e. neither ($\delta(\varphi(\mathrm{red}_1 V)) = \mathrm{red}_2 V$ together with $\varphi(\delta(\varphi(\mathrm{red}_1 V))) \ne \mathrm{red}_1 V$) nor ($\mathrm{red}_1 V = \varphi(\mathrm{red}_2 V)$ together with $\varphi(\delta(\varphi(\mathrm{red}_2 V))) \ne \mathrm{red}_2 V$), and assume that $\mathrm{red}_2 V$ is either a supersingular place or not fixed in the sense $\varphi(\delta(\varphi(\mathrm{red}_2 V))) = \mathrm{red}_2 V$. Then there is $s \in SS$ with $\mathrm{red}_1 V = s_1$ and $\mathrm{red}_2 V = s_2$.
--
--   This is the place-level form, at level $\Gamma_H$ and $p \parallel M$, of the statement that a point of the special fibre of the Deligne–Rapoport model lying on both components is a supersingular crossing: a place whose two readings collide without being strict of either type must reduce to a supersingular node pair. It is used in the construction of prolongation data for the mod-$p$ de Rham model of $X_H$, in [`ModularCurve.XHDRModelAtP.exists_pic0Mk_eq_forall_isStrict_or_reduceFst_mem_of_prolongationDatum_offDiag_of_wgen`](thm.html#ModularCurve.XHDRModelAtP.exists_pic0Mk_eq_forall_isStrict_or_reduceFst_mem_of_prolongationDatum_offDiag_of_wgen).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JHPlaceSpecialization_exists_mem_reduceFst_eq_reduceSnd_eq_of_not_isStrictFst_of_not_isStrictSnd.lean

import Mathlib
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_JHPlaceSpecialization

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve
open scoped MatrixGroups

theorem ModularCurve.JHPlaceSpecialization.exists_mem_reduceFst_eq_reduceSnd_eq_of_not_isStrictFst_of_not_isStrictSnd
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (θ : ↥(xHFunctionFieldBar M H) ≃ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (α β : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hα : α.IsIntegral) (hβ : β.IsIntegral)
    (δ : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) → Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)))
    (SS : Finset (Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) × Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A))))
    (hSS : ∀ s, s ∈ SS ↔ s ∈ ssNodePairsQExp (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p)
    (Psp : JHPlaceSpecialization p M H hpM A)
    (hTD : Psp.TypeDichotomy α β hα hβ δ)
    (V : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H))
    (h₁ : ¬ Psp.IsStrictFst α β hα hβ δ V) (h₂ : ¬ Psp.IsStrictSnd α β hα hβ δ V)
    (hss : Psp.reduceSnd β hβ δ V ∈ ssPlacesQExp (ResidueField ↥A) (JHNeronObjectAtP.ΓN p M H hpM) p ∨
      ¬ JHPlaceSpecialization.Fixed (p := p) (M := M) (H := H) (hpM := hpM) (A := A) δ (Psp.reduceSnd β hβ δ V)) :
    ∃ s ∈ SS, Psp.reduceFst α hα V = s.1 ∧ Psp.reduceSnd β hβ δ V = s.2 := by sorry
