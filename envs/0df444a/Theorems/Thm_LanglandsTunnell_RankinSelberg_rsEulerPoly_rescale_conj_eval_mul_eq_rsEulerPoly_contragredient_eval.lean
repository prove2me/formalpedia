-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_rsEulerPoly_rescale_conj_eval_mul_eq_rsEulerPoly_contragredient_eval
-- name    : LanglandsTunnell.RankinSelberg.rsEulerPoly_rescale_conj_eval_mul_eq_rsEulerPoly_contragredient_eval
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:09.28874+00:00
-- url     : https://prove2.me/theorems/1fcff53c-4a28-59a3-bff7-a1b0d6891625
-- title:
--   Rescaled conjugate Rankin–Selberg Euler factor at qX
-- statement:
--   For a commutative ring $R$ and $a,b,e_1,e_2,e_3\in R$, `rsEulerPoly` denotes the degree-$6$ polynomial $1-ae_1X+(a^2e_2+be_1^2-2be_2)X^2+(-a^3e_3-abe_1e_2+3abe_3)X^3+(a^2be_1e_3-2b^2e_1e_3+b^2e_2^2)X^4-ab^2e_2e_3X^5+b^3e_3^2X^6$; in both instances occurring here the last argument is $0$, so each side is the quartic $1-ae_1X+(a^2e_2+be_1^2-2be_2)X^2-abe_1e_2X^3+b^2e_2^2X^4$ in the remaining four parameters. The assertion is: let $q$ be a real number with $q>0$, let $a,b\in\mathbb{C}$ with $b\neq 0$ and $\lVert b\rVert=q$, assume $\bar a\,b=q\,a$, and let $X\in\mathbb{C}$. Then the value at $qX$ of `rsEulerPoly` with parameters $(a/q,\;b/q^2,\;\bar a/q,\;\bar b/q^2,\;0)$ equals the value at $X$ of `rsEulerPoly` with parameters $(a/b,\;b^{-1},\;a,\;b,\;0)$, where $\bar{\phantom{a}}$ is complex conjugation (`starRingEnd ℂ`).
--
--   In the Rankin–Selberg part of the Langlands–Tunnell input, this identifies the local Euler factor attached to a unitarily rescaled unramified $\mathrm{GL}_2$ parameter pair $(a/q,b/q^2)$ paired with its conjugate, after the change of variable $X\mapsto qX$, with the Euler factor of the contragredient parameter pair $(a/b,b^{-1})$ paired with $(a,b)$; the hypotheses $\lVert b\rVert=q$ and $\bar a b=qa$ express that conjugation sends the Satake roots to $q$ divided by those roots. It is used in the construction of Rankin–Selberg test data over $\mathbb{Q}$ and in the comparison of the Godement–Eisenstein global integral of a form with itself against the Euler product of `rsEulerPoly`.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_rsEulerPoly_rescale_conj_eval_mul_eq_rsEulerPoly_contragredient_eval.lean

import Definitions.Def_LanglandsTunnell_RankinSelbergEuler

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Polynomial LanglandsTunnell.RankinSelberg

theorem LanglandsTunnell.RankinSelberg.rsEulerPoly_rescale_conj_eval_mul_eq_rsEulerPoly_contragredient_eval
    (q : ℝ) (hq : 0 < q) (a b : ℂ) (hb : b ≠ 0) (hnorm : ‖b‖ = q)
    (hconj : (starRingEnd ℂ) a * b = (q : ℂ) * a) (X : ℂ) :
    (rsEulerPoly (a / q) (b / q ^ 2) ((starRingEnd ℂ) a / q) ((starRingEnd ℂ) b / q ^ 2) 0).eval ((q : ℂ) * X) =
      (rsEulerPoly (a / b) b⁻¹ a b 0).eval X := by sorry
