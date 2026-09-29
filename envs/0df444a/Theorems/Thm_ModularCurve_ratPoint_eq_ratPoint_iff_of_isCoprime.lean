-- Prove2me | Theorems.Thm_ModularCurve_ratPoint_eq_ratPoint_iff_of_isCoprime
-- name    : ModularCurve.ratPoint_eq_ratPoint_iff_of_isCoprime
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:54.618386+00:00
-- url     : https://prove2.me/theorems/6ea43388-53a5-59b1-918f-b834013d43a5
-- title:
--   Coprime integral coordinates on P¹(ℚ) are unique up to sign
-- statement:
--   For integers $a, c, a', c'$ the map [`ModularCurve.ratPoint`](def/ModularCurve_CuspSpace.html#L11) sends a pair $(a,c)$ to the point of the one-point compactification `OnePoint ℚ` given by $\infty$ if $c = 0$ and by the image of the rational number $a/c$ otherwise. The theorem assumes that $a$ and $c$ are coprime in $\mathbb{Z}$ (in the Bézout sense of `IsCoprime`, i.e. there exist $x, y$ with $xa + yc = 1$) and likewise that $a'$ and $c'$ are coprime, and asserts the equivalence: [`ModularCurve.ratPoint a c`](def/ModularCurve_CuspSpace.html#L11) equals [`ModularCurve.ratPoint a' c'`](def/ModularCurve_CuspSpace.html#L11) if and only if either $a = a'$ and $c = c'$, or $a = -a'$ and $c = -c'$. Thus a point of $\mathbb{P}^1(\mathbb{Q})$, presented in this chart form, determines its coprime integral homogeneous coordinates up to a single global sign.
--
--   This is the standard uniqueness of normalised homogeneous coordinates for points of $\mathbb{P}^1(\mathbb{Q})$, the elementary input for putting cusps of $\Gamma_0(N)$ into a normal form. It is used by [`ModularCurve.CuspSpace.normalFormCriterion`](thm.html#ModularCurve.CuspSpace.normalFormCriterion) in the treatment of the cusps of the modular curve.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_ratPoint_eq_ratPoint_iff_of_isCoprime.lean

import Mathlib
import Definitions.Def_ModularCurve_CuspSpace
import Definitions.Def_ModularCurve_GenusNumerics

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open OnePoint

theorem ModularCurve.ratPoint_eq_ratPoint_iff_of_isCoprime {a c a' c' : ℤ} (h : IsCoprime a c)
    (h' : IsCoprime a' c') :
    ModularCurve.ratPoint a c = ModularCurve.ratPoint a' c' ↔ (a = a' ∧ c = c') ∨ (a = -a' ∧ c = -c') := by sorry
