-- Prove2me | Theorems.Thm_GaussPart_lemma_3_10
-- name    : GaussPart.lemma_3_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:32:03.536532+00:00
-- url     : https://prove2.me/theorems/b278d3f9-4476-49aa-bce2-79edc9c3ef54
-- title:
--   Lemma 3.10 — negligible total mass of the low-$Q$-mass cells
-- statement:
--   Let $P=N(0,I_d)$ and let $Q$ be $(q,\sigma)$-smooth with respect to $P$. For $t\le L+1$ consider the partition $\mathcal U_t$ of Algorithm 1 and $\mathcal B_t=\{R\in\mathcal U_t:Q(R)\le\xi\}$. Let $m\ge2$ bound the number of children of every refinement, $\kappa\in(0,1)$, and $s=\kappa/(2(\kappa+\log m))$. If every executed split is $\kappa$-Gaussian good, then for every $\lambda\in(0,1)$
--   $$\sum_{R\in\mathcal B_t}Q(R)\le\lambda+\frac1\sigma\Big(\frac{\xi^{2s}}{\lambda^{1/2+s}}\Big)^{1/q},$$
--   and for $\varepsilon\in(0,1)$ the choice $\xi=\big((\sigma\varepsilon)^q\lambda^{1/2+s}\big)^{1/(2s)}$ makes this at most $\lambda+\varepsilon$.
--
--   This bounds the mass discarded by the mass test of Algorithm 1, through the potential $\sum_{R\in\mathcal U_t}(P(R)Q(R))^{1/2-s}$.
--
--   **Formalization Note** Algorithm 1 is a valid trace with knobs $K$; $\xi=K.\xi$, $m=K.m$. $\mathcal B_t$ is selected by true mass. "Every executed split is $\kappa$-Gaussian good" is `SplitsGood Q K tr κ`.
--
--   Differences from the source:
--   - encoding: "Let Q be (q, σ)-smooth with respect to P" → P = N(0, I_d), with q ≥ 1 and σ ∈ (0, 1]; reason: the ranges are part of Definition 1.1, and P is the Gaussian reference of Algorithm 1 ("κ-Gaussian good")
--   - generalization: Algorithm 1 through iteration L → any valid trace (GaussPart.Trace): any threshold whose empirical gap is at least 2g instead of a maximizing one, and any refinement (sorted breakpoints, gaps ≤ δ₀, ends beyond ±T, at most m pieces) instead of the exact grid of Definition 3.4; reason: the analysis uses only these properties; Algorithm 1 with Definition 3.4's grid is one valid trace
--   - generalization: every executed split is κ-Gaussian good → assumed only on cells of positive Q-mass; reason: fewer assumptions; Q | R is undefined when Q(R) = 0
-- source:
--   Diakonikolas, Iakovidis, Kane, Ma, Gaussian Partitioning for Reliable Learning of Multi-Index Models, arXiv:2611.05264 (sha256 7e0ca6d4…), Lemma 3.10, p.23 (PDF p.25); Algorithm 1, p.19

import Mathlib
import Definitions.Def_GaussPart_IsSmooth
import Definitions.Def_GaussPart_Trace
import Definitions.Def_GaussPart_TraceEvents

open MeasureTheory ProbabilityTheory

namespace GaussPart

/-- **Lemma 3.10** (Negligible Total Mass of Low-Q-Mass Cells).

arXiv:2611.05264 (copy with sha256 7e0ca6d4…), Lemma 3.10, p.23 (PDF p.25); Algorithm 1, p.19.

"Let Q be (q, σ)-smooth with respect to P. For t ≤ L + 1, consider the partition U_t of Algorithm 1,
and let B_t = {R ∈ U_t : Q(R) ≤ ξ}. Let m ≥ 2 bound the number of children in every refinement, and
set s = κ/(2(κ + log m)). Assuming that every executed split is κ-Gaussian good, for every
λ ∈ (0, 1), ∑_{R∈B_t} Q(R) ≤ λ + (1/σ)(ξ^{2s}/λ^{1/2+s})^{1/q}. In particular, for ε ∈ (0, 1), the
choice ξ = ((σε)^q λ^{1/2+s})^{1/(2s)} makes this total Q-mass at most λ + ε."

**Formalization Note.**
* `P = N(0, I_d)` and the standing ranges `q ≥ 1`, `σ ∈ (0, 1]` of §3; `κ ∈ (0, 1)` as in
  Definition 3.4.
* "Algorithm 1" is a valid `Trace` with parameters `K`; `ξ = K.ξ` and `m = K.m` (a trace has
  `m ≥ 2` and every refinement has at most `m` children). `B_t` is selected by true mass
  (`lowMassCells`), not by the algorithm's tag. "Every executed split is κ-Gaussian good" is
  `SplitsGood Q K tr κ`, on cells of positive `Q`-mass.
* Real powers are `Real.rpow`; `log` is natural. -/
theorem lemma_3_10 {d : ℕ} (Q : Measure (Vec d)) [IsProbabilityMeasure Q] (q σ : ℝ) (hq : 1 ≤ q)
    (hσ : 0 < σ) (hσ1 : σ ≤ 1) (hs : IsSmooth (stdGaussian (Vec d)) Q q σ) (K : Knobs) (κ : ℝ)
    (hκ : 0 < κ) (hκ1 : κ < 1) (tr : Trace d) (htr : tr.IsValid K)
    (hgood : tr.SplitsGood Q K κ) :
    ∀ t : ℕ, t ≤ K.L + 1 →
      (∀ lam : ℝ, 0 < lam → lam < 1 →
        mass Q (tr.lowMassCells Q t K.ξ) ≤
          lam + 1 / σ * (K.ξ ^ (2 * (κ / (2 * (κ + Real.log K.m)))) /
            lam ^ (1 / 2 + κ / (2 * (κ + Real.log K.m)))) ^ (1 / q)) ∧
      (∀ lam ε : ℝ, 0 < lam → lam < 1 → 0 < ε → ε < 1 →
        K.ξ = ((σ * ε) ^ q * lam ^ (1 / 2 + κ / (2 * (κ + Real.log K.m)))) ^
          (1 / (2 * (κ / (2 * (κ + Real.log K.m))))) →
        mass Q (tr.lowMassCells Q t K.ξ) ≤ lam + ε) := by sorry

end GaussPart
