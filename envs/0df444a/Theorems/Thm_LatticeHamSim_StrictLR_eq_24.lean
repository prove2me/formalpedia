-- Prove2me | Theorems.Thm_LatticeHamSim_StrictLR_eq_24
-- name    : LatticeHamSim.StrictLR.eq_24
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T23:55:00.721053+00:00
-- url     : https://prove2.me/theorems/22718371-036a-4bbc-9386-688ba6ccec38
-- title:
--   (24), p. 23 — C_B(X,t) ≤ C_B(X,0) + Σ_{Z∼X} 2∫₀^t D_B(Z,s) ds for t ≥ 0
-- statement:
--   Let $H = \sum_{X \subseteq \Lambda} h_X$ be a Hamiltonian on a finite metric space of sites $\Lambda$ with local dimension $q$, where every $h_X$ is Hermitian and supported on $X$, and let $B$ be any operator. Let $C_B$ and $D_B$ be the quantities of displays (18)–(19). For every set $X$ of sites and every $t \ge 0$,
--   $$C_B(X, t) \le C_B(X, 0) + \sum_{Z \,:\, Z \sim X} 2 \int_0^{t} D_B(Z, s)\, ds,$$
--   where the sum runs over all sets $Z$ of sites meeting $X$.
--
--   This integral inequality controls how fast an operator initially supported on $X$ can fail to commute with $B$; it is the first step of the proof of every Lieb–Robinson bound in Appendix C.
--
--   **Formalization Note** The paper writes the upper limit as $|t|$; the statement is given for $t \ge 0$, where $|t| = t$. For $t < 0$ the paper's derivation pairs $C_B(X, t)$ with $D_B(Z, -s)$, so the literal display with $D_B(Z, s)$ is not what the derivation gives there. The integrand $s \mapsto D_B(Z, s)$ is continuous, so the interval integral is a genuine integral. The operator $B$ is arbitrary; its support is not used. $\|\cdot\|$ is the $L^2$ operator norm.
-- source:
--   Haah, Hastings, Kothari and Low, Quantum algorithm for simulating real time evolution of lattice Hamiltonians, arXiv:1801.03922v4, p. 23, Appendix C.2, display (24)

import Mathlib
import Definitions.Def_LatticeHamSim_StrictLR_Setting
open scoped Matrix.Norms.L2Operator

namespace LatticeHamSim.StrictLR

theorem eq_24 {Λ : Type*} [Fintype Λ] [DecidableEq Λ] [MetricSpace Λ] {q : ℕ}
    (h : Finset Λ → Matrix (Λ → Fin q) (Λ → Fin q) ℂ)
    (hherm : ∀ X, (h X).IsHermitian) (hsupp : ∀ X, LatticeHamSim.CommLR.SupportedOn X (h X))
    (B : Matrix (Λ → Fin q) (Λ → Fin q) ℂ) (X : Finset Λ) (t : ℝ) (ht : 0 ≤ t) :
    LatticeHamSim.CommLR.CB h B X t ≤ LatticeHamSim.CommLR.CB h B X 0 +
      ∑ Z ∈ Finset.univ.filter (fun Z => LatticeHamSim.CommLR.meets Z X), 2 * ∫ s in (0 : ℝ)..t, LatticeHamSim.CommLR.DB h B Z s := by sorry

end LatticeHamSim.StrictLR
