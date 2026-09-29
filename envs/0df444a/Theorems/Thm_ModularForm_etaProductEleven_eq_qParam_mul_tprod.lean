-- Prove2me | Theorems.Thm_ModularForm_etaProductEleven_eq_qParam_mul_tprod
-- name    : ModularForm.etaProductEleven_eq_qParam_mul_tprod
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.335791+00:00
-- url     : https://prove2.me/theorems/e5b2faeb-cb2c-5524-998a-ac86b13a2bf5
-- title:
--   q-product expansion of η(z)²η(11z)²
-- statement:
--   The assertion is an identity of complex numbers, with a single variable $z \in \mathbb{C}$ and no hypotheses: the square of Dedekind's eta function at $z$ times the square of eta at $11z$ equals $q_1(z)$, the period-$1$ parameter $q_1(z) = e^{2\pi i z}$ of `Function.Periodic.qParam`, multiplied by the product of two squares of unrestricted infinite products $\prod'_{n : \mathbb{N}}$, the first with $n$-th factor $1 -$ `ModularForm.eta_q n z` and the second with $n$-th factor $1 -$ `ModularForm.eta_q n (11z)`; here `ModularForm.eta_q n w` is the $q$-power occurring in the $n$-th factor of Mathlib's eta product at $w$, so that the two products are $\prod_{n \ge 1}(1 - q^n)$ and $\prod_{n \ge 1}(1 - q^{11n})$ with $q = e^{2\pi i z}$. Thus the classical identity $\eta(z)^2\eta(11z)^2 = q\prod_{n\ge1}(1-q^n)^2(1-q^{11n})^2$ is recorded, the two fractional prefactors $q^{2/24}$ and $q^{22/24}$ of the eta factors combining into the integer power $q^1$. The identity is stated for every $z$, with no convergence or half-plane restriction, the infinite products being Mathlib's unconditional `tprod`.
--
--   The function $\eta(z)^2\eta(11z)^2$ is the eta-product expression of the weight-$2$ newform of level $11$ attached to $X_0(11)$, and this identity is its $q$-expansion in the shape $q\prod(1-q^n)^2(1-q^{11n})^2$. It is used to establish the $1$-periodicity of this eta product ([`ModularForm.etaProductEleven_add_one`](thm.html#ModularForm.etaProductEleven_add_one)) and its vanishing at the cusp $\infty$, en route to the non-vanishing of $S_2(\Gamma_0(11))$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularForm_etaProductEleven_eq_qParam_mul_tprod.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem ModularForm.etaProductEleven_eq_qParam_mul_tprod (z : ℂ) :
    ModularForm.eta z ^ 2 * ModularForm.eta (11 * z) ^ 2 =
      Function.Periodic.qParam 1 z *
        ((∏' n : ℕ, (1 - ModularForm.eta_q n z)) ^ 2 *
          (∏' n : ℕ, (1 - ModularForm.eta_q n (11 * z))) ^ 2) := by sorry
