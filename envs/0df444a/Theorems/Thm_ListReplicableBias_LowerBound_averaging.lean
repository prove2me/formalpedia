-- Prove2me | Theorems.Thm_ListReplicableBias_LowerBound_averaging
-- name    : ListReplicableBias.LowerBound.averaging
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:23:47.952673+00:00
-- url     : https://prove2.me/theorems/f09fa7ef-6f6f-40cb-864c-42d3d542e1a3
-- title:
--   §5.4 display — A frequent accurate output, with the full chain
-- statement:
--   Let $A$ be $(d+1,\varepsilon,\delta)$-list replicable, with $\varepsilon>0$ and $0<\delta<1/8$. For every $p\in[0,1]^d$ there exist a nonempty valid list $L_p$ and an output $y\in L_p$ for which
--   $$\Pr_p(Y=y)\ge\frac{1-\delta}{|L_p|}\ge\frac7{8(d+1)}\ge\frac1{2(d+1)}.$$
--   Here $|L_p|\le d+1$, every member is $\varepsilon$-close to $p$, and $\Pr_p(Y\in L_p)\ge1-\delta$.
--
--   The statement supplies a frequent accurate output without choosing a unique maximizer or imposing a measurable tie-breaking rule. The list is nonempty because its probability is positive.
--
--   Differences from the source:
--   - encoding: $\mathbb R^d$ with $\ell_\infty$ distance → functions on `Fin d` with their sup norm; reason: this reindexes the same finite coordinates and preserves every distance
--   - encoding: arbitrary randomized adaptive sampling algorithms and full histories → an arbitrary probability seed space, prefix-dependent coin choices, and the explicit transcript density; failure is `none`; reason: all private randomness is included in the seed, earlier choices are recoverable from it and earlier outcomes, and ignored tosses pad a fixed cap without changing the output law
--   - encoding: real event probabilities → the real value of the nonnegative transcript measure on the event; reason: valid biases make this measure a probability law, so conversion to a real number loses no mass
--   - encoding: the chosen most likely output and its probability chain → existence of a valid list and a member realizing the entire probability chain; reason: every maximizer realizes this bound, while the bound itself needs no specific tie-breaking convention
--   - generalization: the averaging display in the regime epsilon,delta in (0,1/8) → every epsilon>0, retaining delta in (0,1/8); reason: the averaging argument uses only list mass and cardinality; the source accuracy regime is included
-- source:
--   Chen, Bastan, Pavan, Vinodchandran, The Price of List Replicability: Tight Bounds for Bias Estimation, STOC 2027 submission #681 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/681.pdf, §5.4 display, PDF p. 6 (arbitrary-transcript extension: Appendix B, PDF p. 15)

import Mathlib
import Definitions.Def_ListReplicableBias_LowerBound_ListReplicability

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace ListReplicableBias.LowerBound

/-- §5.4 averaging display, PDF p. 6; Appendix B, PDF p. 15.
A witness list and one of its members realize every link of the displayed chain. -/
theorem averaging {d N : ℕ} (A : SamplingAlgorithm d N) (ε δ : ℝ)
    (hε : 0 < ε) (hδ : δ ∈ Set.Ioo (0 : ℝ) (1 / 8))
    (hA : IsListReplicable A (d + 1) ε δ)
    (p : Fin d → ℝ) (hp : p ∈ cube d 0 1) :
    ∃ L : Finset (Fin d → ℝ), L.Nonempty ∧ L.card ≤ d + 1 ∧
      (∀ y ∈ L, ‖y - p‖ ≤ ε) ∧
      1 - δ ≤ outputProb A p (some '' (L : Set (Fin d → ℝ))) ∧
      ∃ y ∈ L,
        (1 - δ) / (L.card : ℝ) ≤ outputProb A p {some y} ∧
        (7 : ℝ) / (8 * ((d : ℝ) + 1)) ≤ (1 - δ) / (L.card : ℝ) ∧
        (1 : ℝ) / (2 * ((d : ℝ) + 1)) ≤ (7 : ℝ) / (8 * ((d : ℝ) + 1)) := by sorry

end ListReplicableBias.LowerBound
