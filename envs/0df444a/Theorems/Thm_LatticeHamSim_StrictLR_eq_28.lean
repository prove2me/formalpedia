-- Prove2me | Theorems.Thm_LatticeHamSim_StrictLR_eq_28
-- name    : LatticeHamSim.StrictLR.eq_28
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T23:55:07.529901+00:00
-- url     : https://prove2.me/theorems/0acda57b-4f80-42f4-b031-1fbfe080717c
-- title:
--   (28), p. 23 — C_B(Z,0) ≤ 2‖B‖δ_{Z∼Y}, C_B(Z,t) ≤ 2‖B‖, D_B(Z,0) ≤ 2‖B‖‖h_Z‖δ_{Z∼Y}, D_B(Z,t) ≤ 2‖B‖‖h_Z‖
-- statement:
--   Let $H = \sum_{X \subseteq \Lambda} h_X$ be a Hamiltonian on a finite metric space of sites $\Lambda$ with local dimension $q$, where every $h_X$ is Hermitian and supported on $X$. Let $B$ be an operator supported on a set $Y$ of sites, and let $C_B$, $D_B$ be the commutator quantities of displays (18)–(19). Then for every set $Z$ of sites and every real $t$,
--   $$C_B(Z, 0) \le 2\|B\|\,\delta_{Z \sim Y}, \qquad C_B(Z, t) \le 2\|B\|,$$
--   $$D_B(Z, 0) \le 2\|B\|\,\|h_Z\|\,\delta_{Z \sim Y}, \qquad D_B(Z, t) \le 2\|B\|\,\|h_Z\|,$$
--   where $\delta_{Z \sim Y} = 1$ if $Z \cap Y \neq \emptyset$ and $0$ otherwise.
--
--   These are the elementary bounds that start the iteration in Appendix C: operators with disjoint supports commute, and Heisenberg evolution preserves the operator norm.
--
--   **Formalization Note** $\|\cdot\|$ is the $L^2$ operator norm on matrices.
-- source:
--   Haah, Hastings, Kothari and Low, Quantum algorithm for simulating real time evolution of lattice Hamiltonians, arXiv:1801.03922v4, p. 23, Appendix C.2, display (28)

import Mathlib
import Definitions.Def_LatticeHamSim_StrictLR_Setting
open scoped Matrix.Norms.L2Operator

namespace LatticeHamSim.StrictLR

theorem eq_28 {Λ : Type*} [Fintype Λ] [DecidableEq Λ] [MetricSpace Λ] {q : ℕ}
    (h : Finset Λ → Matrix (Λ → Fin q) (Λ → Fin q) ℂ)
    (hherm : ∀ X, (h X).IsHermitian) (hsupp : ∀ X, LatticeHamSim.CommLR.SupportedOn X (h X))
    (B : Matrix (Λ → Fin q) (Λ → Fin q) ℂ) (Y : Finset Λ) (hB : LatticeHamSim.CommLR.SupportedOn Y B)
    (Z : Finset Λ) (t : ℝ) :
    LatticeHamSim.CommLR.CB h B Z 0 ≤ 2 * ‖B‖ * (if LatticeHamSim.CommLR.meets Z Y then 1 else 0) ∧
    LatticeHamSim.CommLR.CB h B Z t ≤ 2 * ‖B‖ ∧
    LatticeHamSim.CommLR.DB h B Z 0 ≤ 2 * ‖B‖ * ‖h Z‖ * (if LatticeHamSim.CommLR.meets Z Y then 1 else 0) ∧
    LatticeHamSim.CommLR.DB h B Z t ≤ 2 * ‖B‖ * ‖h Z‖ := by sorry

end LatticeHamSim.StrictLR
