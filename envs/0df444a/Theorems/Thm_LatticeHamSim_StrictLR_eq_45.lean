-- Prove2me | Theorems.Thm_LatticeHamSim_StrictLR_eq_45
-- name    : LatticeHamSim.StrictLR.eq_45
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T23:55:25.480311+00:00
-- url     : https://prove2.me/theorems/d36d94b5-3f70-4e49-b856-448cbe5cc275
-- title:
--   (45), p. 27 — Σ_{Q:P∼Q∼S} ‖h_Q‖ ≤ ζ₀ Σ_{p∈P} δ_{dist(p,S)≤1}
-- statement:
--   Let $(h_Q)_{Q \subseteq \Lambda}$ be operators indexed by the subsets of a finite metric space of sites $\Lambda$ (local dimension $q$), strictly local in the sense that $h_Q = 0$ whenever $\mathrm{diam}(Q) > 1$, and let $\zeta_0$ be a real number with
--   $$\sum_{Q \ni x} |Q|\, \|h_Q\| \le \zeta_0 \quad \text{for every site } x .$$
--   Then for arbitrary sets $P, S$ of sites,
--   $$\sum_{Q \,:\, P \sim Q \sim S} \|h_Q\| \le \zeta_0 \sum_{p \in P} \delta_{\mathrm{dist}(p, S) \le 1},$$
--   where the left sum is over all $Q$ meeting both $P$ and $S$, and $\delta_{\mathrm{dist}(p, S) \le 1}$ is $1$ if $\mathrm{dist}(p, S) \le 1$ and $0$ otherwise.
--
--   This counting bound converts the linked sums of (44) into powers of $\zeta_0$.
--
--   **Formalization Note** The paper defines $\zeta_0 = \max_{x} \sum_{Q \ni x} |Q|\,\|h_Q\|$; here $\zeta_0$ is any upper bound of these sums. The two readings are equivalent for this inequality, which is monotone in $\zeta_0$ and is satisfied by the maximum itself; the bound form avoids a maximum over a possibly empty $\Lambda$. $\mathrm{dist}(p, S)$ is `Metric.infDist` (which is $0$ for $S = \emptyset$, where the left side is an empty sum). $\|\cdot\|$ is the $L^2$ operator norm.
-- source:
--   Haah, Hastings, Kothari and Low, Quantum algorithm for simulating real time evolution of lattice Hamiltonians, arXiv:1801.03922v4, p. 27, Appendix C.4, display (45)

import Mathlib
import Definitions.Def_LatticeHamSim_StrictLR_Setting
open scoped Matrix.Norms.L2Operator

namespace LatticeHamSim.StrictLR

theorem eq_45 {Λ : Type*} [Fintype Λ] [DecidableEq Λ] [MetricSpace Λ] {q : ℕ}
    (h : Finset Λ → Matrix (Λ → Fin q) (Λ → Fin q) ℂ)
    (hloc : ∀ X : Finset Λ, 1 < Metric.diam (X : Set Λ) → h X = 0)
    (ζ₀ : ℝ) (hζ₀ : ∀ x : Λ, ∑ Q ∈ Finset.univ.filter (fun Q => x ∈ Q), (Q.card : ℝ) * ‖h Q‖ ≤ ζ₀)
    (P S : Finset Λ) :
    ∑ Q ∈ Finset.univ.filter (fun Q => LatticeHamSim.CommLR.meets P Q ∧ LatticeHamSim.CommLR.meets Q S), ‖h Q‖ ≤
      ζ₀ * ∑ p ∈ P, (if Metric.infDist p (S : Set Λ) ≤ 1 then (1 : ℝ) else 0) := by sorry

end LatticeHamSim.StrictLR
