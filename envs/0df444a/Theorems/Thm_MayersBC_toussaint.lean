-- Prove2me | Theorems.Thm_MayersBC_toussaint
-- name    : MayersBC.toussaint
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T15:56:46.840028+00:00
-- url     : https://prove2.me/theorems/7f1c0f1e-8086-46c5-b3f3-ce78ada699c3
-- title:
--   Section d, p.8 — Toussaint's inequality $1 - BW \le K/2$
-- statement:
--   Let $p_0, p_1$ be probability distributions on a finite set $J$, and let
--
--   $$
--   BW(p_0, p_1) = \sum_{j \in J} p_0(j)^{1/2}\, p_1(j)^{1/2}, \qquad K(p_0,p_1) = \sum_{j\in J} |p_0(j) - p_1(j)| .
--   $$
--
--   Then
--
--   $$
--   1 - BW(p_0, p_1) \le \frac{K(p_0, p_1)}{2} .
--   $$
--
--   Mayers applies it to the outcome distributions of a measurement on $\rho_0, \rho_1$: together with $K \le 4\varepsilon$ it gives $BW \ge 1 - 2\varepsilon$.
--
--   Differences from the source:
--   - generalization: BW and K of the outcome distributions Pr(J_0 = j), Pr(J_1 = j) of a measurement → any two probability distributions on a finite set; reason: the inequality cited from [15] holds for all distributions; outcome distributions are a special case
--   - encoding: BW = Σ_j Pr(J_0 = j)^{1/2} Pr(J_1 = j)^{1/2} → FuchsVdGraaf.bhattacharyya p0 p1 = Σ_j √(p0(j) p1(j)); reason: the two expressions agree for nonnegative values
-- source:
--   Mayers, The Trouble with Quantum Bit Commitment, arXiv:quant-ph/9603015v3, section d, p.8

import Mathlib
import Definitions.Def_FuchsVdGraaf_IsProbDist
import Definitions.Def_FuchsVdGraaf_bhattacharyya
import Definitions.Def_MayersBC_kolmogorov

namespace MayersBC

/-- Mayers, arXiv:quant-ph/9603015v3, section d, p.8: "It is explained in [15] that
(1 − BW) ≤ K/2", where `BW = Σ_{j∈A} Pr(J_0 = j)^{1/2} Pr(J_1 = j)^{1/2}` is the
Bhattacharyya–Wootters overlap and `K = Σ_j |p_0(j) − p_1(j)|` the Kolmogorov distance (no ½).
For any two probability distributions `p_0, p_1` on a finite set, `1 − BW(p_0, p_1) ≤ K(p_0, p_1)/2`.

**Formalization Note.** `BW` is the published `FuchsVdGraaf.bhattacharyya`,
`Σ_j √(p_0(j) p_1(j))`, which equals `Σ_j √p_0(j) √p_1(j)` for nonnegative values. Distributions
are the published `FuchsVdGraaf.IsProbDist`. -/
theorem toussaint {J : Type} [Fintype J] (p0 p1 : J → ℝ)
    (h0 : FuchsVdGraaf.IsProbDist p0) (h1 : FuchsVdGraaf.IsProbDist p1) :
    1 - FuchsVdGraaf.bhattacharyya p0 p1 ≤ kolmogorov p0 p1 / 2 := by sorry

end MayersBC
