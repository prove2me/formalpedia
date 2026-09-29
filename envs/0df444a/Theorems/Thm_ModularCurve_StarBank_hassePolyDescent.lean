-- Prove2me | Theorems.Thm_ModularCurve_StarBank_hassePolyDescent
-- name    : ModularCurve.StarBank.hassePolyDescent
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.379182+00:00
-- url     : https://prove2.me/theorems/37f6ded8-5704-5737-8913-1fdf1ea40a52
-- title:
--   Integral descent: T = G(j) Δ^N with deg G = N
-- statement:
--   Let $N$ be a natural number and let $F$ be a modular form of weight $12N$ for the full modular group. Suppose $T$ is a power series with integer coefficients whose image under the coefficientwise map $\mathbb{Z}\to\mathbb{C}$ is the $q$-expansion of $F$ of width $1$, and suppose the constant coefficient of $T$ is non-zero. Then there exists a polynomial $G$ with integer coefficients such that: the degree of $G$ is exactly $N$; the coefficient of $X^N$ in $G$ is the constant coefficient of $T$; and, in the field of Laurent series over $\mathbb{Z}$, the image of $T$ equals $G$ evaluated at [`ModularCurve.jqModC ℤ`](def/ModularCurve_JqCoeff.html#L15) multiplied by the $N$-th power of $q\cdot\big(\prod_{n\ge 1}(1-q^{n})\big)^{24}$, that is, of the Laurent series $\Delta$ obtained from `HahnSeries.single (1 : ℤ) 1` times the twenty-fourth power of the formal product [`ModularCurve.etaProd`](def/ModularCurve_X0.html#L119) $=\prod_{n\ge 1}(1-X^{n})$. Here [`ModularCurve.jqModC ℤ`](def/ModularCurve_JqCoeff.html#L15) is the integral Laurent-series model of $j$, defined as $q^{-1}$ times the power series [`ModularCurve.jNum`](def/ModularCurve_X0.html#L142) $=$ `eisenstein4`$^3\cdot$`dedekindEtaUnitInv` (coefficients transported along $\mathbb{Z}\to\mathbb{Z}$). So $T = G(j)\,\Delta^{N}$ with $\deg G = N$ and leading coefficient the constant term of $T$.
--
--   This is the integral refinement, with exact degree and leading coefficient, of the classical fact that a level-one form of weight $12N$ is a polynomial of degree at most $N$ in $j$ times $\Delta^{N}$; the hypothesis that the constant term be non-zero is what forces the degree to be exactly $N$. It is used in the construction of modular units on $X_0(N)$, in particular by [`ModularCurve.StarBank.starBank`](thm.html#ModularCurve.StarBank.starBank) and by [`ModularCurve.exists_natDegree_eq_sub_one_and_modularUnit_intCast_eq_aeval_jqModC_of_charP`](thm.html#ModularCurve.exists_natDegree_eq_sub_one_and_modularUnit_intCast_eq_aeval_jqModC_of_charP), and rests on the corresponding statement over $\mathbb{C}$ together with the identifications of the $q$-expansions of $\Delta$ and of $E_4^3/\Delta$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_StarBank_hassePolyDescent.lean

import Definitions.Def_ModularCurve_JqCoeff
import Mathlib.NumberTheory.ModularForms.LevelOne.DimensionFormula

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open Polynomial HahnSeries ModularCurve UpperHalfPlane
open scoped MatrixGroups

theorem ModularCurve.StarBank.hassePolyDescent {N : ℕ}
    (F : ModularForm 𝒮ℒ (12 * (N : ℤ))) {T : PowerSeries ℤ}
    (hT : T.map (Int.castRingHom ℂ) = UpperHalfPlane.qExpansion 1 ⇑F)
    (h0 : PowerSeries.constantCoeff T ≠ 0) :
    ∃ G : Polynomial ℤ, G.natDegree = N ∧ G.coeff N = PowerSeries.constantCoeff T ∧
      HahnSeries.ofPowerSeries ℤ ℤ T
        = Polynomial.aeval (ModularCurve.jqModC ℤ) G
          * (HahnSeries.single (1 : ℤ) 1
              * HahnSeries.ofPowerSeries ℤ ℤ ModularCurve.etaProd ^ 24) ^ N := by sorry
