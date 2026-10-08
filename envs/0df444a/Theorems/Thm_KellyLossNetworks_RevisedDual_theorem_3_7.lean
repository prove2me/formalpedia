-- Prove2me | Theorems.Thm_KellyLossNetworks_RevisedDual_theorem_3_7
-- name    : KellyLossNetworks.RevisedDual.theorem_3_7
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T11:09:16.49975+00:00
-- url     : https://prove2.me/theorems/bca6fcfa-05d6-4c6a-ab11-e038b4eb1be6
-- title:
--   Theorem 3.7 — the Erlang fixed point is E_j = 1 − exp(−y_j) for the unique optimum y of the revised dual (3.5)
-- statement:
--   Consider a loss network with $J$ links and a finite set of routes: link $j$ has $C_j\ge1$ circuits, a call on route $r$ uses $A_{jr}\in\mathbb Z_+$ circuits of link $j$, and calls on route $r$ arrive at rate $\nu_r>0$. Let $E(\nu,C)$ be Erlang's formula and $U$ the utilization function (3.4).
--
--   The equations
--   $$E_j=E(\rho_j,C_j),\qquad \rho_j=(1-E_j)^{-1}\sum_rA_{jr}\nu_r\prod_i(1-E_i)^{A_{ir}},\qquad j=1,\dots,J, \tag{3.1–3.2}$$
--   have a unique solution $(E_1,\dots,E_J)$, given in terms of the optimum $y$ of the revised dual problem
--   $$\text{minimize}\quad\sum_r\nu_r\exp\Big(-\sum_jy_jA_{jr}\Big)+\sum_j\int_0^{y_j}U(z,C_j)\,dz\qquad\text{subject to }y\ge0 \tag{3.5}$$
--   by
--   $$E_j=1-\exp(-y_j),\qquad j=1,\dots,J.$$
--   Precisely: (3.5) has an optimum $y$, every optimum of (3.5) equals $y$, and a vector $E\in[0,1]^J$ solves (3.1)–(3.2) if and only if $E_j=1-e^{-y_j}$ for every $j$.
--
--   The Erlang fixed point is the standard reduced-load approximation for blocking in circuit-switched networks. The theorem identifies it with the solution of a strictly convex program, a relaxation of the dual problem (2.3) whose solution gives the limiting blocking probabilities; this yields the uniqueness of the fixed point under fixed routing and a way to compute it.
--
--   **Formalization Note** The equations (3.1)–(3.2) are the published `KellyStochasticNetworks.ErlangFixedPoint`, and solutions are sought in $[0,1]^J$, the range the paper uses on p. 338. The hypotheses $\nu_r>0$ and $C_j\ge1$ are the paper's implicit standing assumptions. Existence and uniqueness of the solution alone is the Proved platform theorem `KellyStochasticNetworks.erlang_fixed_point_unique`; this statement adds the identification with the optimum of (3.5).
-- source:
--   Kelly, Loss networks, Ann. Appl. Probab. 1(3):319–378 (1991), DOI 10.1214/aoap/1177005872, p. 338, Theorem 3.7

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Erlang
import Definitions.Def_KellyStochasticNetworks_LossNetwork
import Definitions.Def_KellyLossNetworks_RevisedDual_Problem

namespace KellyLossNetworks.RevisedDual

/-- **Theorem 3.7.** Equations (3.1) and (3.2) have a unique solution `(E_1, …, E_J)`, given in
terms of the optimum `y` of the revised dual problem (3.5) by `E_j = 1 − exp(−y_j)`.

Stated as: if `ν_r > 0` for every route and `C_j ≥ 1` for every link, the revised dual problem
(3.5) has an optimum `y`, every optimum equals `y`, and a vector `E` is a solution of
(3.1)–(3.2) in `[0, 1]^J` if and only if `E_j = 1 − exp(−y_j)` for every `j`.

Kelly, Loss networks, Ann. Appl. Probab. 1(3):319–378 (1991), DOI 10.1214/aoap/1177005872,
p. 338, Theorem 3.7.

**Formalization Note.** (3.1)–(3.2) is the published `KellyStochasticNetworks.ErlangFixedPoint`
with Erlang's formula `KellyStochasticNetworks.erlang`; solutions are sought in `[0, 1]^J`, the
range the paper uses on p. 338. The hypotheses `ν_r > 0` and `C_j ≥ 1` are the paper's implicit
standing assumptions (a link with `C_j = 0` makes (3.4) meaningless). Existence and uniqueness of
the solution alone is the Proved platform theorem
`KellyStochasticNetworks.erlang_fixed_point_unique`; this statement adds that the solution is
`1 − exp(−y)` for the optimum `y` of (3.5). -/
theorem theorem_3_7 {J R : ℕ} (A : Fin J → Fin R → ℕ) (ν : Fin R → ℝ)
    (C : Fin J → ℕ) (hν : ∀ r, 0 < ν r) (hC : ∀ j, 1 ≤ C j) :
    ∃ y : Fin J → ℝ, IsRevisedDualOptimum A ν C y ∧
      (∀ y' : Fin J → ℝ, IsRevisedDualOptimum A ν C y' → y' = y) ∧
      ∀ E : Fin J → ℝ,
        ((∀ j, E j ∈ Set.Icc (0 : ℝ) 1) ∧ KellyStochasticNetworks.ErlangFixedPoint A ν C E) ↔
          E = fun j => 1 - Real.exp (-y j) := by sorry

end KellyLossNetworks.RevisedDual
