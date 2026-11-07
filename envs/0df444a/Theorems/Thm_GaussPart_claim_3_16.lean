-- Prove2me | Theorems.Thm_GaussPart_claim_3_16
-- name    : GaussPart.claim_3_16
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:32:13.514312+00:00
-- url     : https://prove2.me/theorems/fd3b62bb-b32c-4f9a-91e4-c9743977eb5e
-- title:
--   Claim 3.16 — mass stopped by rejection or failed split validation
-- statement:
--   In the proof of Theorem 3.1 ($P=N(0,I_d)$, $Q$ $(q,\sigma)$-smooth, $\eta,\delta,\Delta\in(0,1/2)$), with the Parameter Choices of Algorithm 1 for a constant $C_0$ at least the one of Lemma 3.5, and on the success event $\Omega$: the cells $\mathcal E$ of the final partition stopped by finder rejection or by failed split validation satisfy
--   $$\sum_{R\in\mathcal E}Q(R)\le\frac{\eta}{100}.$$
--
--   Together with Claim 3.15 this bounds the uncertified mass by $6\eta/100<\eta$.
--
--   **Formalization Note** "$C_0$ at least the constant of Lemma 3.5" is the hypothesis `GoodSplitConstants C₀ C` for some $C>1$. Algorithm 1 is a valid trace with the knobs of `params C₀ k q σ η δ Δ`; the parts of $\Omega$ used are hypotheses on cells of positive $Q$-mass: empirical tails within $g/4$, the direction conclusion of Corollary C.1, and the contrapositive of its no-reject conclusion with the $H$ of the Parameter Choices.
--
--   Differences from the source:
--   - generalization: Algorithm 1 through iteration L → any valid trace (GaussPart.Trace): any threshold whose empirical gap is at least 2g instead of a maximizing one, and any refinement (sorted breakpoints, gaps ≤ δ₀, ends beyond ±T, at most m pieces) instead of the exact grid of Definition 3.4; reason: the analysis uses only these properties; Algorithm 1 with Definition 3.4's grid is one valid trace
--   - encoding: "C₀ at least the constant required by Lemma 3.5" → hypothesis GoodSplitConstants C₀ C for some C > 1; reason: the existence part of Lemma 3.5 holds with C₀, which is what the proof uses
--   - generalization: on Ω (every amplified finder satisfies Corollary C.1, every empirical CDF within g/4) → only the CDF event and the direction and no-reject conclusions, on cells of positive Q-mass; reason: fewer assumptions; Q | R is undefined when Q(R) = 0
-- source:
--   Diakonikolas, Iakovidis, Kane, Ma, Gaussian Partitioning for Reliable Learning of Multi-Index Models, arXiv:2611.05264 (sha256 7e0ca6d4…), Claim 3.16, p.27 (PDF p.29); success event Ω, p.26; Parameter Choices, p.21

import Mathlib
import Definitions.Def_GaussPart_IsSmooth
import Definitions.Def_GaussPart_hellingerSq
import Definitions.Def_GaussPart_Trace
import Definitions.Def_GaussPart_Params
import Definitions.Def_GaussPart_TraceEvents

open MeasureTheory ProbabilityTheory

namespace GaussPart

/-- **Claim 3.16** (Mass Stopped by Rejection or Failed Split Validation).

arXiv:2611.05264 (copy with sha256 7e0ca6d4…), Claim 3.16, p.27 (PDF p.29), in the proof of
Theorem 3.1; the success event `Ω` is on p.26; the Parameter Choices of Algorithm 1 on p.21.

"The remaining terminal collection satisfies ∑_{R∈E} q_R ≤ η/100."

**Formalization Note.**
* `P = N(0, I_d)`, `Q` `(q, σ)`-smooth, and the ranges of Theorem 3.1. The Parameter Choices
  (`params C₀ k q σ η δ ∆`) use a constant `C₀` "at least the constant required by Lemma 3.5": the
  hypothesis `GoodSplitConstants C₀ C` for some `C > 1` (the existence part of Lemma 3.5 holds with
  `C₀`).
* "Algorithm 1" is a valid `Trace` with the knobs of these parameters. The parts of `Ω` the claim
  uses are hypotheses: every empirical tail used for validation is within `g/4` of the population
  tail (`TailsAccurate`), every returned direction satisfies item 1 of Corollary C.1
  (`FinderDirSound`), and every rejection satisfies the contrapositive of item 3
  (`FinderRejectSound`, with the `H` of p.21). All three are imposed only on cells of positive
  `Q`-mass.
* `E` is the list of cells of `U_{L+1}` tagged as stopped by rejection or failed validation;
  `q_R = Q(R)`. -/
theorem claim_3_16 (C₀ C : ℝ) (hC₀ : 1 < C₀) (hC : 1 < C) (hlemma : GoodSplitConstants C₀ C)
    {d : ℕ} (hd : 1 ≤ d) (k : ℕ) (hk : 1 ≤ k) (q σ η δ Δ : ℝ) (hq : 1 ≤ q) (hσ : 0 < σ)
    (hσ1 : σ ≤ 1) (hη : 0 < η) (hη1 : η < 1 / 2) (hδ : 0 < δ) (hδ1 : δ < 1 / 2) (hΔ : 0 < Δ)
    (hΔ1 : Δ < 1 / 2) (Q : Measure (Vec d)) [IsProbabilityMeasure Q]
    (hs : IsSmooth (stdGaussian (Vec d)) Q q σ) (tr : Trace d)
    (htr : tr.IsValid (params C₀ k q σ η δ Δ).knobs)
    (hcdf : tr.TailsAccurate Q (params C₀ k q σ η δ Δ).knobs ((params C₀ k q σ η δ Δ).g / 4))
    (hdir : tr.FinderDirSound Q (params C₀ k q σ η δ Δ).knobs k Δ)
    (hrej : tr.FinderRejectSound Q (params C₀ k q σ η δ Δ).knobs k (params C₀ k q σ η δ Δ).H) :
    mass Q (tr.tagged ((params C₀ k q σ η δ Δ).L + 1) Tag.err) ≤ η / 100 := by sorry

end GaussPart
