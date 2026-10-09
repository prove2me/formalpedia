-- Prove2me | Theorems.Thm_LatticeHamSim_StrictLR_eq_42
-- name    : LatticeHamSim.StrictLR.eq_42
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T23:55:10.37382+00:00
-- url     : https://prove2.me/theorems/7ae15e11-79fb-4601-9f40-7f471c25dfa2
-- title:
--   (42), p. 26 — C_B(X,t) ≤ C_B(X,0) + 2Σ_{Z:X∼Z}‖h_Z‖∫₀^t C_B(Z,s) ds for t ≥ 0
-- statement:
--   Let $H = \sum_{X \subseteq \Lambda} h_X$ be a Hamiltonian on a finite metric space of sites $\Lambda$ with local dimension $q$, where every $h_X$ is Hermitian and supported on $X$, and let $B$ be any operator. Let $C_B$ be the quantity of display (18). For every set $X$ of sites and every $t \ge 0$,
--   $$C_B(X, t) \le C_B(X, 0) + 2 \sum_{Z \,:\, X \sim Z} \|h_Z\| \int_0^{t} C_B(Z, s)\, ds .$$
--
--   This is the closed recursive inequality for $C_B$ alone, obtained from (24) and $D_B(Z, s) \le \|h_Z\|\, C_B(Z, s)$. Iterating it along chains of overlapping sets gives the strictly local Lieb–Robinson bound.
--
--   **Formalization Note** The paper states (42) "assuming $X \not\sim Y$" (where $B$ is supported on $Y$). The inequality does not use that assumption, and its iteration in (43) applies it to sets that may meet $Y$, so the assumption is dropped: the statement is the more general one. As in (24), the paper's upper limit $|t|$ is stated for $t \ge 0$. The integrand $s \mapsto C_B(Z, s)$ is continuous, so the integral is genuine. $\|\cdot\|$ is the $L^2$ operator norm.
-- source:
--   Haah, Hastings, Kothari and Low, Quantum algorithm for simulating real time evolution of lattice Hamiltonians, arXiv:1801.03922v4, p. 26, Appendix C.4, display (42)

import Mathlib
import Definitions.Def_LatticeHamSim_StrictLR_Setting
open scoped Matrix.Norms.L2Operator

namespace LatticeHamSim.StrictLR

theorem eq_42 {Λ : Type*} [Fintype Λ] [DecidableEq Λ] [MetricSpace Λ] {q : ℕ}
    (h : Finset Λ → Matrix (Λ → Fin q) (Λ → Fin q) ℂ)
    (hherm : ∀ X, (h X).IsHermitian) (hsupp : ∀ X, LatticeHamSim.CommLR.SupportedOn X (h X))
    (B : Matrix (Λ → Fin q) (Λ → Fin q) ℂ) (X : Finset Λ) (t : ℝ) (ht : 0 ≤ t) :
    LatticeHamSim.CommLR.CB h B X t ≤ LatticeHamSim.CommLR.CB h B X 0 +
      2 * ∑ Z ∈ Finset.univ.filter (fun Z => LatticeHamSim.CommLR.meets X Z),
        ‖h Z‖ * ∫ s in (0 : ℝ)..t, LatticeHamSim.CommLR.CB h B Z s := by sorry

end LatticeHamSim.StrictLR
