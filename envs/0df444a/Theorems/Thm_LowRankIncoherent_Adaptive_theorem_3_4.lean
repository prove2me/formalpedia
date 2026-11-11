-- Prove2me | Theorems.Thm_LowRankIncoherent_Adaptive_theorem_3_4
-- name    : LowRankIncoherent.Adaptive.theorem_3_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T13:19:35.534195+00:00
-- url     : https://prove2.me/theorems/c067102d-8eff-422a-981a-7996989a18d3
-- title:
--   Theorem 3.4 (corrected: integer-query rounding for unrestricted ε)
-- statement:
--   There exist absolute constants $K,c>0$, uniform over every dimension, rank, accuracy, confidence and channel, with the following property. Let $a=d_1≥1$, $b=d_2≥2$, $D=ab$, $1≤r≤D$, and $a≤rb$. An admissible pair of measurable selections (an exact rank-$r$ truncation with some tie-breaking, and an exact nearest-channel minimizer) exists, and the conclusions hold for every admissible pair, fixed before the unknown channel. For every $ε>0$, $0<δ<1$, and channel $E$ of Kraus rank at most $r$, run the actual Algorithm 3 with
--   $$s=ε/(64r),\quad T=\max\{1,\lceil\log_2a\rceil\},\quad δ'=δ/(T+1),\quad b_0=D+(1+a/r)\log(6/δ'),\quad n=\lceil Kb_0/s^2\rceil.$$
--   The operational execution law is a probability measure, the decoder and adaptive input functions are measurable, all intermediate input states and logarithms are valid, and the output $\widehat E$ is a channel. Every query uses a fresh purification and an independent Haar-random basis measurement, with only classical information retained. The output minimizes distance over all channels rather than over only rank-$r$ channels. It satisfies
--   $$\Pr\{\|\widehat E-E\|_⋄>ε\}≤δ.$$
--   With the exact executed query count $Q=2n(T+1)$ and exactly $T$ adaptive updates,
--   $$Q≤2(T+1)+c\frac{r^2}{ε^2}\log(2a)\left[D+(1+a/r)\log\frac{18\log(2a)}δ\right],\qquad T≤c\log(2a).$$
--   For every $0<ε≤2$ the same universal $c$ also satisfies unchanged equation (43), obtained by dropping the additive $2(T+1)$ above. This retains all confidence parameters and all feasible channels, including boundary dimensions and channels with no spectral gap.
--
--   The global correction accounts only for integer query rounding. The theorem remains an end-to-end algorithmic error and resource guarantee rather than an existence statement about a favorable input. The structural selections never receive $E$ and contain no assumed accuracy property.
--
--   Differences from the source:
--   - correction: equation (43) for every positive accuracy without ceiling overhead → the exact rounded count Q is bounded by 2(T+1) plus (43) globally, and by unchanged (43) for 0<ε≤2; reason: for a=1,b=2,r=1,δ=1/3,E(z)=z|0⟩⟨0|, b0=2+2 log 36 and Q=4 ceil(4096 K b0/ε²)≥4; for any K,c>0 choose ε>max{64 sqrt(K b0),sqrt(c log 2 [2+2 log(54 log 2)]/4)}, so Q=4 while (43)<4
--   - encoding: Algorithm 3 with unspecified tie splitting and nearest-channel argmin → existence of admissible measurable selections, the guarantee for every admissible selection fixed before the unknown channel, explicit Haar/Born execution laws, and their normalization and valid-state conclusions; reason: this makes the operational probability and unspecified measurable choices precise without adding a good-event or accuracy hypothesis
-- source:
--   Aadil Oufkir, Kean Chen, STOC 2027 submission #364 (October 2026), Theorem 3.4 and Algorithm 3, printed pp. 19–20 = PDF pp. 19–20 (= Theorem 1.2, p. 3); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/364.pdf

import Definitions.Def_LowRankIncoherent_Adaptive_Algorithm

open Matrix MeasureTheory
open scoped MatrixOrder ComplexOrder ENNReal
noncomputable section

namespace LowRankIncoherent.Adaptive

/-- Theorem 3.4, with literal ceiling overhead for unrestricted positive accuracy.
For d1=1,d2=2,r=1,δ=1/3, Algorithm 3 always uses at least four queries,
whereas the printed uncorrected bound tends to zero as ε tends to infinity.
The printed bound is retained without change when ε ≤ 2.
An admissible implementation of the tie-breaking truncation and the nearest-channel choice
exists, and the guarantee holds for every admissible implementation of Algorithm 3. -/
theorem theorem_3_4 : ∃ K c : ℝ, 0 < K ∧ 0 < c ∧
    ∀ a b r : ℕ, 0 < a → 2 ≤ b → 1 ≤ r → r ≤ a*b → a ≤ r*b →
    (∃ p : Choices a b, Admissible r p) ∧
    ∀ p : Choices a b, Admissible r p →
    ∀ ε δ : ℝ, 0 < ε → 0 < δ → δ < 1 →
    ∀ E : Map a b, E ∈ ChanTomoNB.QChan r a b →
    let n := algN K a b r ε δ
    let μ := executionLaw K p E r ε δ
    Measurable (experimentLaw (ι := Fin b × Fin a)) ∧
    Measurable (fun X : Joint a b => pairLaw X n) ∧
    Measurable (decode K p r ε δ) ∧
    Measurable (rhoFrom (n := n) p r (scale r ε)) ∧
    Measurable (finalInput (n := n) p r (scale r ε)) ∧
    (∀ t, IsProbabilityMeasure (selectionLaw (n := n) p E r (scale r ε) t)) ∧
    IsProbabilityMeasure μ ∧
    (∀ᵐ data ∂μ,
      data.1.length = rounds a ∧
      (∀ zs ∈ data.1.tails,
        State (rhoFrom p r (scale r ε) zs) ∧ (rhoFrom p r (scale r ε) zs).PosDef ∧
        State (mixture (rhoFrom p r (scale r ε) zs)) ∧
        LE ((1/(2*(a : ℂ))) • 1) (mixture (rhoFrom p r (scale r ε) zs))) ∧
      (∀ z zs, z :: zs ∈ data.1.tails →
        let ρ := rhoFrom p r (scale r ε) zs
        let A := clip r (twoBatch p.truncate (mixture ρ) (scale r ε) z).2
        A.PosDef ∧ 0 < rt (expM (logM ρ + logM A))) ∧
      State (finalInput p r (scale r ε) data.1) ∧
      LE ((1/(2*(a : ℂ))) • 1) (finalInput p r (scale r ε) data.1) ∧
      unchoi (decode K p r ε δ data) ∈ ChanTomoNB.QChan (a*b) a b) ∧
    μ {data | ChanTomoNB.diamondDist (unchoi (decode K p r ε δ data)) E > ε}
      ≤ ENNReal.ofReal δ ∧
    (queries K a b r ε δ : ℝ) ≤ 2*(rounds a+1) + printedBound c a b r ε δ ∧
    (ε ≤ 2 → (queries K a b r ε δ : ℝ) ≤ printedBound c a b r ε δ) ∧
    (rounds a : ℝ) ≤ c * Real.log (2*a) := by sorry

end LowRankIncoherent.Adaptive
