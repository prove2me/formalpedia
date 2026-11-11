-- Prove2me | Theorems.Thm_GainShareOpt_StochBalance_lemma_12
-- name    : GainShareOpt.StochBalance.lemma_12
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T03:49:16.681645+00:00
-- url     : https://prove2.me/theorems/76b80155-a886-44c0-afd0-c95f0f7fd27a
-- title:
--   Lemma 12 — normalization: Programs (31) and (73) have the same value, $1/2\le\gamma^*\le1-1/e$
-- statement:
--   Programs (31) and (73) have the same supremal value $\gamma^*$, and
--   $$\tfrac12\le\gamma^*\le1-1/e<1 .$$
--   Moreover:
--   1. for every feasible pair $(\gamma,f)$ of (31) with $\gamma>1/e$, replacing $f$ by $\bar f=\min\{f,1-1/e\}$ keeps $\bar f\in F_0$ and $\Phi_1,\Phi_2$ unchanged, and $g=1-\bar f$ lies in $G$ with $A(g)=\Phi_1(f)$ and $\min_{0\le\ell\le\sigma\le1}H_g(\sigma,\ell)=\Phi_2(f)$;
--   2. conversely, every $g\in G$ comes from some $f\in F_0$ with $f=1-g$ on $[0,1]$, $\Phi_1(f)=A(g)$ and $\Phi_2(f)=\min_{0\le\ell\le\sigma\le1}H_g(\sigma,\ell)$.
--
--   It moves the problem to the fixed domain $[0,1]$, where the Volterra comparison applies.
--
--   Differences from the source:
--   - encoding: f ∈ F0 a function [0, ∞) → [0, 1] → f : ℝ → ℝ, with continuity, monotonicity and the range [0, 1] required on Set.Ici 0 only; reason: Lean convention; values on negative reals never enter any test, so the same instances
--   - reading: replacing f by min{f, 1 − 1/e} and setting g = 1 − min{f, 1 − 1/e} preserves both constraint values → the truncation lies in F0 with the same Φ1, Φ2, and g ∈ G has A(g) = Φ1(f) and min H_g = Φ2(f); reason: the two constraint values of (31) are Φ1, Φ2 and those of (73) are A, min H_g; this is what the proof establishes
--   - reading: every g ∈ G corresponds to an admissible original function with the same constraint values → ∃ f ∈ F0 with f = 1 − g on [0, 1], Φ1(f) = A(g), Φ2(f) = min H_g; reason: 'corresponds' is the correspondence g = 1 − f on [0, 1] used throughout the lemma
-- source:
--   Pan Xu, Gain-Sharing Optimization in Randomized Primal–Dual Analysis: Structure and Certification, arXiv:2503.09508 (held copy of 2026-10-31, sha256 d28f3b77…6c70b), p. 49, Lemma 12

import Mathlib
import Definitions.Def_GainShareOpt_StochBalance_CertFunctional
import Definitions.Def_GainShareOpt_StochBalance_Canonical
import Definitions.Def_GainShareOpt_StochBalance_Normalized

namespace GainShareOpt.StochBalance

/-- Lemma 12 (normalization): Programs (31) and (73) have the same supremal value `γ*`,
`1/2 ≤ γ* ≤ 1 - 1/e < 1`; truncation at `1 - 1/e` and `g = 1 - min{f, 1 - 1/e}` preserve both
constraint values of a feasible pair with value `> 1/e`; every `g ∈ G` comes from an admissible `f`
with the same constraint values. -/
theorem lemma_12 :
    gammaStar = gamma73 ∧ 1 / 2 ≤ gammaStar ∧ gammaStar ≤ 1 - Real.exp (-1) ∧
    1 - Real.exp (-1) < 1 ∧
    (∀ (γ : ℝ) (f : ℝ → ℝ), Feasible31 γ f → Real.exp (-1) < γ →
      (fun z => min (f z) (1 - Real.exp (-1))) ∈ F0 ∧
      Phi1 (fun z => min (f z) (1 - Real.exp (-1))) = Phi1 f ∧
      Phi2 (fun z => min (f z) (1 - Real.exp (-1))) = Phi2 f ∧
      (fun z => 1 - min (f z) (1 - Real.exp (-1))) ∈ ClassG ∧
      scoreA (fun z => 1 - min (f z) (1 - Real.exp (-1))) = Phi1 f ∧
      minTestH (fun z => 1 - min (f z) (1 - Real.exp (-1))) = Phi2 f) ∧
    (∀ g ∈ ClassG, ∃ f ∈ F0, (∀ z ∈ Set.Icc (0 : ℝ) 1, f z = 1 - g z) ∧
      Phi1 f = scoreA g ∧ Phi2 f = minTestH g) := by sorry

end GainShareOpt.StochBalance
