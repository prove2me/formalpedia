-- Prove2me | Theorems.Thm_LanglandsTunnell_RankinSelberg_mk_heckeRecursionSeq_mul_heckeRecursionSeq_mul_coe_rsEulerPoly_eq_and_hasSum
-- name    : LanglandsTunnell.RankinSelberg.mk_heckeRecursionSeq_mul_heckeRecursionSeq_mul_coe_rsEulerPoly_eq_and_hasSum
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:09.28874+00:00
-- url     : https://prove2.me/theorems/70ce77ff-928c-5687-817b-0c332472bdca
-- title:
--   Rankin–Selberg identity for two Hecke recursion sequences
-- statement:
--   Let $N,\lambda,\omega,\lambda',\omega'$ be complex numbers. Write $(u_m)_{m\ge 0}$ for the sequence `heckeRecursionSeq N lam om`, defined by $u_0=1$, $u_1=\lambda/N$ and $u_{m+2}=(\lambda u_{m+1}-\omega u_m)/N$, and $(u'_m)$ for the same recursion built from $(\lambda',\omega')$; division in $\mathbb{C}$ is the Mathlib one, so $N=0$ gives $u_m=0$ for $m\ge 1$. Put $a=\lambda/N$, $b=\omega/N$, $a'=\lambda'/N$, $b'=\omega'/N$, and let $R$ be the polynomial `rsEulerPoly a b a' b' 0`, that is, specialising its third elementary parameter to $0$, $$R(X)=1-aa'X+(a^2b'+b a'^2-2bb')X^2-aba'b'X^3+b^2b'^2X^4.$$ Three assertions are made. First, in $\mathbb{C}[[X]]$ the power series $\sum_{m\ge 0}u_mu'_mX^m$ satisfies $\bigl(\sum_{m\ge0}u_mu'_mX^m\bigr)\cdot R(X)=1-bb'X^2$. Secondly, $\lVert u_m\rVert\le M^m$ for all $m$, where $M=\max(1,\lVert a\rVert+\lVert b\rVert)$. Thirdly, for every $x\in\mathbb{C}$ with $\lVert x\rVert\,MM'<1$, where $M'=\max(1,\lVert a'\rVert+\lVert b'\rVert)$, one has $R(x)\ne 0$, the family $\bigl(u_mu'_mx^m\bigr)_{m\in\mathbb{N}}$ is summable with sum $(1-bb'x^2)/R(x)$, and the family indexed by $m\in\mathbb{Z}$ of $\,\mathrm{torusFactor}(N,\lambda,\omega,m)\cdot\mathrm{torusFactor}(N,\lambda',\omega',m)\cdot x^m$, whose terms vanish for $m<0$ and equal $u_mu'_mx^m$ for $m\ge 0$, is summable with the same sum.
--
--   This is the algebraic identity underlying the unramified Rankin–Selberg computation for $\mathrm{GL}_2\times\mathrm{GL}_2$: for $1-aX+bX^2=(1-\alpha_1X)(1-\alpha_2X)$ and $1-a'X+b'X^2=(1-\gamma_1X)(1-\gamma_2X)$, the sequences $u_m$, $u'_m$ are the complete homogeneous symmetric functions $h_m(\alpha_1,\alpha_2)$, $h_m(\gamma_1,\gamma_2)$, and $R(X)=\prod_{i,j}(1-\alpha_i\gamma_jX)$, so that $\sum_m h_mh'_mX^m=(1-\alpha_1\alpha_2\gamma_1\gamma_2X^2)/R(X)$, here with both the formal and the convergent form on the disc $\lVert x\rVert MM'<1$. It is used in the evaluation of the local torus integral in `exists_hasProd_rsFinIntegral_eq_rsFinIntegral_indicator_mul_of_torus_law`.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_RankinSelberg_mk_heckeRecursionSeq_mul_heckeRecursionSeq_mul_coe_rsEulerPoly_eq_and_hasSum.lean

import Definitions.Def_UnramifiedWhittaker_HeckeRecursion
import Definitions.Def_LanglandsTunnell_RankinSelbergEuler
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open UnramifiedWhittaker LanglandsTunnell.RankinSelberg

theorem LanglandsTunnell.RankinSelberg.mk_heckeRecursionSeq_mul_heckeRecursionSeq_mul_coe_rsEulerPoly_eq_and_hasSum
    (N lam om lam' om' : ℂ) :
    PowerSeries.mk (fun m : ℕ => heckeRecursionSeq N lam om m * heckeRecursionSeq N lam' om' m) *
        (rsEulerPoly (lam / N) (om / N) (lam' / N) (om' / N) 0 : PowerSeries ℂ) =
      1 - PowerSeries.C (om / N * (om' / N)) * PowerSeries.X ^ 2 ∧
    (∀ m : ℕ, ‖heckeRecursionSeq N lam om m‖ ≤ (max 1 (‖lam / N‖ + ‖om / N‖)) ^ m) ∧
    ∀ x : ℂ, ‖x‖ * (max 1 (‖lam / N‖ + ‖om / N‖) * max 1 (‖lam' / N‖ + ‖om' / N‖)) < 1 →
      (rsEulerPoly (lam / N) (om / N) (lam' / N) (om' / N) 0).eval x ≠ 0 ∧
      HasSum (fun m : ℕ => heckeRecursionSeq N lam om m * heckeRecursionSeq N lam' om' m * x ^ m)
        ((1 - om / N * (om' / N) * x ^ 2) / (rsEulerPoly (lam / N) (om / N) (lam' / N) (om' / N) 0).eval x) ∧
      HasSum (fun m : ℤ => torusFactor N lam om m * torusFactor N lam' om' m * x ^ m)
        ((1 - om / N * (om' / N) * x ^ 2) / (rsEulerPoly (lam / N) (om / N) (lam' / N) (om' / N) 0).eval x) := by sorry
