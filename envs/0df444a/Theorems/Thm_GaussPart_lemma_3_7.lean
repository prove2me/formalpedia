-- Prove2me | Theorems.Thm_GaussPart_lemma_3_7
-- name    : GaussPart.lemma_3_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:31:48.174018+00:00
-- url     : https://prove2.me/theorems/62b2ee43-e42a-4c1e-b5aa-214057645986
-- title:
--   Lemma 3.7 — the mass of the active cells decreases exponentially
-- statement:
--   Let $P=N(0,I_d)$, let $Q$ be $(q,\sigma)$-smooth with respect to $P$ ($q\ge1$, $\sigma\in(0,1]$), $r=dQ/dP$, and assume $M\ge1$, $\tau_0\in[0,1]$ with $Q(r>M)\le\tau_0$. Let $g>0$ be the split-validation parameter, $L\ge1$, and $\kappa\in(0,1)$ with $\kappa\le g^2/2$. Consider Algorithm 1 through iteration $L$, on the event that every empirical tail used to validate a split is within $g/4$ of the population tail $\Pr_{x\sim Q\mid R}[v\cdot x\ge s]$ at every threshold. If $A_t$ denotes the cells split in round $t$, then for every $t\in[L]$
--   $$\sum_{R\in A_t}Q(R)\le\sqrt M\,e^{-\kappa(t-1)}+\tau_0 .$$
--   In particular, for $\eta\in(0,1)$ and $L=1+\lceil\kappa^{-1}\log(100\sqrt M/\eta)\rceil$, both the cells split in round $L$ and the leaves still unprocessed after round $L$ have total $Q$-mass at most $\eta/100+\tau_0$.
--
--   This bounds the recursion depth of Algorithm 1, through the potential $\sum_{R\in A_t}\sqrt{P(R)Q(R)}$.
--
--   **Formalization Note** "Algorithm 1 through iteration $L$" is a valid trace with knobs $K$ ($K.L=L$, $K.g=g$); the CDF event is the hypothesis `TailsAccurate Q K tr (g/4)`. $t-1$ is computed in the reals.
--
--   Differences from the source:
--   - generalization: Algorithm 1 through iteration L → any valid trace (GaussPart.Trace): any threshold whose empirical gap is at least 2g instead of a maximizing one, and any refinement (sorted breakpoints, gaps ≤ δ₀, ends beyond ±T, at most m pieces) instead of the exact grid of Definition 3.4; reason: the analysis uses only these properties; Algorithm 1 with Definition 3.4's grid is one valid trace
--   - generalization: the event holds at every validation stage → the event is assumed only on cells of positive Q-mass; reason: Q | R is undefined when Q(R) = 0; fewer assumptions make the statement stronger
--   - reading: "makes their total mass at most η/100 + τ₀" → stated both for the cells split in round L and for the active cells of U_{L+1}; reason: the proof (p.22) applies the bound to the unprocessed leaves; stating both is the stronger reading
-- source:
--   Diakonikolas, Iakovidis, Kane, Ma, Gaussian Partitioning for Reliable Learning of Multi-Index Models, arXiv:2611.05264 (sha256 7e0ca6d4…), Lemma 3.7, p.21 (PDF p.23); Algorithm 1, p.19

import Mathlib
import Definitions.Def_GaussPart_IsSmooth
import Definitions.Def_GaussPart_Trace
import Definitions.Def_GaussPart_TraceEvents

open MeasureTheory ProbabilityTheory

namespace GaussPart

/-- **Lemma 3.7** (Mass of Active Cells Decreases Exponentially).

arXiv:2611.05264 (copy with sha256 7e0ca6d4…), Lemma 3.7, p.21 (PDF p.23); Algorithm 1, p.19.

"Let P = N(0, I_d), let Q be (q, σ)-smooth with respect to P, where q ≥ 1 and σ ∈ (0, 1], and write
r = dQ/dP. Assume M ≥ 1 and τ₀ ∈ [0, 1] such that Q(r > M) ≤ τ₀. Let g > 0 be the split-validation
parameter used by Algorithm 1. Let L ∈ ℕ₊ and κ ∈ (0, 1) satisfy κ ≤ g²/2. Consider Algorithm 1
through iteration L. Assume the event that all empirical CDFs used to validate splits in these
iterations differ from their population CDFs by at most g/4 at every threshold. For t ∈ [L], denote
by A_t the cells that are split in round t, and write p_R = P(R) and q_R = Q(R). Then
∑_{R∈A_t} q_R ≤ √M e^{−κ(t−1)} + τ₀. In particular, for η ∈ (0, 1), setting
L = 1 + ⌈κ^{−1} log(100√M/η)⌉ makes their total mass at most η/100 + τ₀."

**Formalization Note.**
* "Algorithm 1 through iteration L" is a valid `Trace` with parameters `K` (`K.L = L`, `K.g = g`);
  the mass estimates, finder outputs and empirical tails are free data of the trace, and the CDF
  event is the hypothesis `TailsAccurate Q K tr (g/4)` (on cells of positive `Q`-mass; `Q | R` is
  undefined otherwise). A trace allows any validated threshold and any refinement of the binary
  split, not only the maximizer and the grid of Definition 3.4.
* `A_t` is `tr.splitCells t`, the cells split in round `t`. The last sentence is stated both for
  `A_L` and for the leaves still unprocessed after round `L` (the active cells of `U_{L+1}`), which
  the proof on p.22 calls "their". `t − 1` is computed in `ℝ`. -/
theorem lemma_3_7 {d : ℕ} (Q : Measure (Vec d)) [IsProbabilityMeasure Q] (q σ : ℝ) (hq : 1 ≤ q)
    (hσ : 0 < σ) (hσ1 : σ ≤ 1) (hs : IsSmooth (stdGaussian (Vec d)) Q q σ) (M τ₀ : ℝ) (hM : 1 ≤ M)
    (hτ₀ : 0 ≤ τ₀) (hτ₀1 : τ₀ ≤ 1)
    (hr : Q {x | ENNReal.ofReal M < Q.rnDeriv (stdGaussian (Vec d)) x} ≤ ENNReal.ofReal τ₀)
    (K : Knobs) (κ : ℝ) (hκ : 0 < κ) (hκ1 : κ < 1) (hκg : κ ≤ K.g ^ 2 / 2)
    (tr : Trace d) (htr : tr.IsValid K) (hcdf : tr.TailsAccurate Q K (K.g / 4)) :
    (∀ t : ℕ, 1 ≤ t → t ≤ K.L →
      mass Q (tr.splitCells t) ≤ Real.sqrt M * Real.exp (-(κ * ((t : ℝ) - 1))) + τ₀) ∧
    (∀ η : ℝ, 0 < η → η < 1 →
      K.L = 1 + ⌈κ⁻¹ * Real.log (100 * Real.sqrt M / η)⌉₊ →
        mass Q (tr.splitCells K.L) ≤ η / 100 + τ₀ ∧
        mass Q (tr.tagged (K.L + 1) Tag.active) ≤ η / 100 + τ₀) := by sorry

end GaussPart
