-- Prove2me | Theorems.Thm_KellyLossNetworks_RevisedDual_fixedPoint_iff_stationarity
-- name    : KellyLossNetworks.RevisedDual.fixedPoint_iff_stationarity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T11:09:12.043803+00:00
-- url     : https://prove2.me/theorems/3f582051-b37f-444b-87c2-9f9a0a821033
-- title:
--   §3.1, p. 338 — under E_j = 1 − exp(−y_j) the equations (3.1)–(3.2) become (3.6)
-- statement:
--   Consider a loss network with route rates $\nu_r>0$, link capacities $C_j\ge1$ and incidence matrix $A=(A_{jr})$ with entries in $\mathbb Z_+$. The **Erlang fixed point equations** are
--   $$E_j=E(\rho_j,C_j),\qquad \rho_j=(1-E_j)^{-1}\sum_rA_{jr}\nu_r\prod_i(1-E_i)^{A_{ir}},\qquad j=1,\dots,J, \tag{3.1–3.2}$$
--   where $E(\nu,C)$ is Erlang's formula.
--
--   1. Every solution $(E_1,\dots,E_J)\in[0,1]^J$ of (3.1)–(3.2) has $E_j<1$ for every $j$; hence it is of the form $E_j=1-e^{-y_j}$ with $y_j=-\log(1-E_j)\ge0$.
--   2. For every $y\in\mathbb R^J$ with $y\ge0$, the vector $E_j=1-e^{-y_j}$ solves (3.1)–(3.2) if and only if $y$ satisfies the stationarity conditions (3.6),
--   $$\sum_rA_{jr}\,\nu_r\exp\Big(-\sum_iy_iA_{ir}\Big)=U(y_j,C_j),\qquad j=1,\dots,J.$$
--
--   Together with the characterization of (3.6) as the optimality conditions of (3.5), this turns the fixed point problem into a strictly convex minimization.
--
--   **Formalization Note** The equations (3.1)–(3.2) are the published `KellyStochasticNetworks.ErlangFixedPoint`. Its factor $(1-E_j)^{-1}$ is Lean's inverse, which is $0$ at $E_j=1$; clause 1 shows that no solution in $[0,1]^J$ has $E_j=1$, and in clause 2, $1-E_j=e^{-y_j}>0$.
-- source:
--   Kelly, Loss networks, Ann. Appl. Probab. 1(3):319–378 (1991), DOI 10.1214/aoap/1177005872, pp. 337–338, (3.1), (3.2), and §3.1, the paragraph after (3.6)

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Erlang
import Definitions.Def_KellyStochasticNetworks_LossNetwork
import Definitions.Def_KellyLossNetworks_RevisedDual_Problem

namespace KellyLossNetworks.RevisedDual

/-- **Under `E_j = 1 − exp(−y_j)`, equations (3.1)–(3.2) become (3.6).** Suppose `ν_r > 0` for
every route and `C_j ≥ 1` for every link.
1. A solution `E ∈ [0, 1]^J` of (3.1)–(3.2) has `E_j < 1` for every `j`, so it is the image
   `E_j = 1 − exp(−y_j)` of `y_j = −log(1 − E_j) ≥ 0`.
2. For every `y ≥ 0`, the vector `E_j = 1 − exp(−y_j)` solves (3.1)–(3.2) if and only if `y`
   satisfies the stationarity conditions (3.6).

Kelly, Loss networks, Ann. Appl. Probab. 1(3):319–378 (1991), DOI 10.1214/aoap/1177005872,
p. 338, §3.1, the paragraph after (3.6) (unnumbered).

**Formalization Note.** (3.1)–(3.2) is the published `KellyStochasticNetworks.ErlangFixedPoint`,
whose `(1 - E j)⁻¹` is Lean's inverse (`0` at `E_j = 1`); clause 1 shows that no solution in
`[0, 1]^J` attains `E_j = 1`, and in clause 2 `1 − E_j = exp(−y_j) > 0`. -/
theorem fixedPoint_iff_stationarity {J R : ℕ} (A : Fin J → Fin R → ℕ) (ν : Fin R → ℝ)
    (C : Fin J → ℕ) (hν : ∀ r, 0 < ν r) (hC : ∀ j, 1 ≤ C j) :
    (∀ E : Fin J → ℝ, (∀ j, E j ∈ Set.Icc (0 : ℝ) 1) →
      KellyStochasticNetworks.ErlangFixedPoint A ν C E → ∀ j, E j < 1) ∧
    (∀ y : Fin J → ℝ, (∀ j, 0 ≤ y j) →
      (KellyStochasticNetworks.ErlangFixedPoint A ν C (fun j => 1 - Real.exp (-y j)) ↔
        StationarityConditions A ν C y)) := by sorry

end KellyLossNetworks.RevisedDual
