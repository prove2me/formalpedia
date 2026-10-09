-- Prove2me | Theorems.Thm_LatticeHamSim_StrictLR_eq_46
-- name    : LatticeHamSim.StrictLR.eq_46
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T23:55:17.162616+00:00
-- url     : https://prove2.me/theorems/3a6745a7-1486-4409-85cf-ea6063cf29db
-- title:
--   (46), p. 27 — Σ_{Q:P∼Q} |Q|‖h_Q‖δ_{dist(Q,S)≤d} ≤ ζ₀ Σ_{p∈P} δ_{dist(p,S)≤d+1}
-- statement:
--   Let $(h_Q)_{Q \subseteq \Lambda}$ be operators indexed by the subsets of a finite metric space of sites $\Lambda$ (local dimension $q$), strictly local in the sense that $h_Q = 0$ whenever $\mathrm{diam}(Q) > 1$, and let $\zeta_0$ be a real number with $\sum_{Q \ni x} |Q|\, \|h_Q\| \le \zeta_0$ for every site $x$. Then for arbitrary sets $P, S$ of sites and every real $d$,
--   $$\sum_{Q \,:\, P \sim Q} |Q|\, \|h_Q\|\, \delta_{\mathrm{dist}(Q, S) \le d} \le \zeta_0 \sum_{p \in P} \delta_{\mathrm{dist}(p, S) \le d + 1} .$$
--
--   Together with (45), this inequality bounds each successive factor of a linked sum by $\zeta_0$ while keeping track of the distance still to be covered.
--
--   **Formalization Note** As in (45), $\zeta_0$ is any upper bound of the site sums $\sum_{Q \ni x} |Q|\,\|h_Q\|$, equivalent to the paper's maximum. $\mathrm{dist}(Q, S)$ is `setDist Q S`, the minimum distance for nonempty sets and $0$ if $S = \emptyset$; $\mathrm{dist}(p, S)$ is `Metric.infDist`, also $0$ for $S = \emptyset$. Under these conventions the inequality still holds when $S = \emptyset$. $\|\cdot\|$ is the $L^2$ operator norm.
-- source:
--   Haah, Hastings, Kothari and Low, Quantum algorithm for simulating real time evolution of lattice Hamiltonians, arXiv:1801.03922v4, p. 27, Appendix C.4, display (46)

import Mathlib
import Definitions.Def_LatticeHamSim_StrictLR_Setting
open scoped Matrix.Norms.L2Operator

namespace LatticeHamSim.StrictLR

theorem eq_46 {Λ : Type*} [Fintype Λ] [DecidableEq Λ] [MetricSpace Λ] {q : ℕ}
    (h : Finset Λ → Matrix (Λ → Fin q) (Λ → Fin q) ℂ)
    (hloc : ∀ X : Finset Λ, 1 < Metric.diam (X : Set Λ) → h X = 0)
    (ζ₀ : ℝ) (hζ₀ : ∀ x : Λ, ∑ Q ∈ Finset.univ.filter (fun Q => x ∈ Q), (Q.card : ℝ) * ‖h Q‖ ≤ ζ₀)
    (P S : Finset Λ) (d : ℝ) :
    ∑ Q ∈ Finset.univ.filter (fun Q => LatticeHamSim.CommLR.meets P Q),
        (Q.card : ℝ) * ‖h Q‖ * (if LatticeHamSim.CommLR.setDist Q S ≤ d then 1 else 0) ≤
      ζ₀ * ∑ p ∈ P, (if Metric.infDist p (S : Set Λ) ≤ d + 1 then (1 : ℝ) else 0) := by sorry

end LatticeHamSim.StrictLR
