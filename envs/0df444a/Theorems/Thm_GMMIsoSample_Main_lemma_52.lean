-- Prove2me | Theorems.Thm_GMMIsoSample_Main_lemma_52
-- name    : GMMIsoSample.Main.lemma_52
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T21:33:32.058217+00:00
-- url     : https://prove2.me/theorems/f029e154-0eea-4b8b-b813-d9f398d02322
-- title:
--   Lemma 52 — χ² of the random-direction symmetric two-Gaussian prior against N(0, I_d)^(T)
-- statement:
--   Let $d\ge1$, $r\ge0$, and let $A(r)$ be the prior that outputs $M_{rU}=\tfrac12N(rU,I_d)+\tfrac12N(-rU,I_d)$ for $U\sim\mathrm{Unif}(S^{d-1})$, so $P^{(T)}_{A(0)}=N(0,I_d)^{\otimes T}$. When $Tr^4<d$,
--   $$\chi^2\big(P^{(T)}_{A(r)}\,\big\|\,P^{(T)}_{A(0)}\big)\le\Big(1-\frac{Tr^4}d\Big)^{-1/2}-1,$$
--   and hence if $Tr^4\le d/100$ then $d_{TV}(P^{(T)}_{A(r)},P^{(T)}_{A(0)})\le1/10$.
--
--   It gives the $d/\Gamma_{\min}^4$ lower bound of Proposition 53.
--
--   Differences from the source:
--
--   - encoding: χ²(P‖Q) = E_Q[(dP/dQ − 1)²] → PolySampIso.chiSq, valued in [0, ∞] (∞ unless P ≪ Q); reason: the published definition; a finite bound forces P ≪ Q
--   - encoding: Unif(S^{d−1}) → the law of g/‖g‖ for g ∼ N(0, I_d); reason: this is the rotation-invariant probability on the sphere
--   - encoding: ℝ^d with d ≥ 1 implicit → hypothesis 1 ≤ d; reason: the sphere S^{d−1} requires d ≥ 1
--   - encoding: priors on target distributions → probability measures on Measure(ℝ^d) (Giry σ-algebra); P_A^(T) = A.bind (D ↦ D^{⊗T}); reason: (104)
-- source:
--   Chen, De, Lee, Servedio, Sublinear Sample Size Suffices for Learning Mixtures of Gaussians up to Isometry, STOC 2027 submission (version of November 3, 2026, sha256 411f3581…), p. 68, Lemma 52, (112)–(113)

import Mathlib
import Definitions.Def_PolySampIso_Divergences
import Definitions.Def_GMMIsoSample_Main_Model
import Definitions.Def_GMMIsoSample_Main_LowerBound

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace GMMIsoSample.Main

/-- Lemma 52 (p. 68): in `ℝ^d` (`d ≥ 1`), for `r ≥ 0`, when `Tr⁴ < d`,
`χ²(P_{A(r)}^(T) ‖ P_{A(0)}^(T)) ≤ (1 − Tr⁴/d)^{−1/2} − 1` (112), and if `Tr⁴ ≤ d/100` then
`d_TV(P_{A(r)}^(T), P_{A(0)}^(T)) ≤ 1/10` (113). -/
theorem lemma_52 (d T : ℕ) (r : ℝ) (hd : 1 ≤ d) (hr : 0 ≤ r) :
    ((T : ℝ) * r ^ 4 < d →
      PolySampIso.chiSq (priorAvg (priorSym d r) T) (priorAvg (priorSym d 0) T) ≤
        ENNReal.ofReal ((1 - (T : ℝ) * r ^ 4 / d) ^ (-(1 / 2 : ℝ)) - 1)) ∧
    ((T : ℝ) * r ^ 4 ≤ d / 100 →
      PolySampIso.tvDist (priorAvg (priorSym d r) T) (priorAvg (priorSym d 0) T) ≤ 1 / 10) := by sorry

end GMMIsoSample.Main
