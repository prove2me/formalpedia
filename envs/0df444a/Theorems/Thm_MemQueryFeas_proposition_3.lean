-- Prove2me | Theorems.Thm_MemQueryFeas_proposition_3
-- name    : MemQueryFeas.proposition_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:40:39.878201+00:00
-- url     : https://prove2.me/theorems/a2933028-2827-4a0e-b40c-8cb69b5966dc
-- title:
--   Proposition 3 — Game 1 success $\xi$ forces $I(\mathrm{Message};E^{(i)}\mid E^{(<i)})\ge\xi k\tilde d/(1+\log(\sqrt d/\gamma))-\log2$
-- statement:
--   There is a universal constant $C>0$ such that the following holds. Consider Game 1 with dimensions $d,\tilde d,k$, an invertible linear map $T$, accuracies $\delta^{(0)}\ge\dots\ge\delta^{(N)}>0$, an index $1\le i\le N$ and parameters $\beta,\gamma,\eta$, and suppose
--   $$
--   \delta^{(i-1)}\le\frac1d,\qquad\eta\ge\delta^{(i-1)},\qquad\kappa(T)\le\frac{1}{d(\delta^{(i)}+\dots+\delta^{(N)})},\qquad\frac\gamma\beta\ge Ck\,\frac{\eta}{\delta^{(i-1)}}\sqrt{\frac d{\tilde d}} .
--   $$
--   Then every compression strategy (encoder and decoder with private randomness, no shared randomness) that succeeds with probability at least $\xi>0$ satisfies, in bits,
--   $$
--   I\big(\mathrm{Message};E^{(i)}\mid E^{(<i)}\big)\ \ge\ \xi\cdot\frac{k\tilde d}{1+\log(\sqrt d/\gamma)}-\log 2 .
--   $$
--
--   Producing $k$ robustly independent vectors nearly orthogonal to the hidden subspace requires the message to carry about $k\tilde d$ bits about it; combined with Proposition 2 this rules out the second alternative of the reduction.
--
--   **Formalization Note** $\log$ is base 2, so $\log 2$ is one bit.
--
--   Differences from the source:
--   - encoding: γ/β ≥ Ck(η/δ^(i−1))√(d/d̃), κ(T) ≤ 1/(d(δ^(i)+…+δ^(N))), δ^(i−1) ≤ 1/d → Ck(η/δ^(i−1))√(d/d̃)·β ≤ γ, d(δ^(i)+…+δ^(N))κ(T) ≤ 1, dδ^(i−1) ≤ 1; reason: multiplied out; equal for nonzero denominators, and a zero denominator is read as +∞
--   - encoding: a linear map T; accuracies δ^(≤N) → T invertible; 0 < δ^(N) ≤ … ≤ δ^(0); 1 ≤ i ≤ N; reason: required for NoiseAddition(T(E), δ) to be defined (p.7) and for E^(i−1) to exist
--   - encoding: γ = 0, where log(√d/γ) = +∞ makes the printed bound −log 2 → Lean's √d/0 = 0, so the bound reads ξ·k d̃ − 1 bits at γ = 0; reason: at γ = 0 the hypothesis forces β ≤ 0 (k, d̃ ≥ 1), so winning needs outputs exactly orthogonal to Ẽ^(i), a null event unless the information is infinite; the claim stays true and every γ > 0 is unchanged
--   - generalization: the decoder returns nonzero vectors → any measurable decoder; an output containing a zero vector loses; reason: a decoder that always returns nonzero vectors is a special case with the same winning event
--   - encoding: any compression strategy → measurable encoder and decoder with independent private randomness and a standard Borel message space; reason: the information I(Message; …) is defined for standard Borel messages; the decoder sees only Message and E^(≤i−1) (line 3, "only")
--   - encoding: information in bits (log base 2, p.7) → the nats-valued condMutualInfo compared with ENNReal.ofReal (bits · ln 2); reason: unit conversion; values stay in [0, ∞] (no truncation of ∞)
-- source:
--   Yu–Blanchard, Exponential memory/query-complexity tradeoffs in high-accuracy feasibility problems, preprint (Nov. 3, 2026), Proposition 3, p.13 (PDF p.14)

import Mathlib
import Definitions.Def_MemQueryFeas_IsGame1Play
import Definitions.Def_MemQueryFeas_game1Win
import Definitions.Def_MemQueryFeas_game1Output
import Definitions.Def_MemQueryFeas_condNum
import Definitions.Def_ThompsonTutorial_InfoRatio_condMutualInfo

open MeasureTheory

namespace MemQueryFeas

/-- **Proposition 3 (hardness of the compression game).** Yu–Blanchard, *Exponential memory/query-complexity tradeoffs in high-accuracy feasibility problems*, preprint (Nov. 3, 2026), Proposition 3, p.13 (PDF p.14):
"There is a universal constant `C > 0` such that the following holds. Suppose that
`δ^(i−1) ≤ 1/d`, `η ≥ δ^(i−1)`, and `κ(T) ≤ 1/(d(δ^(i) + … + δ^(N)))` and
`γ/β ≥ Ck (η/δ^(i−1)) √(d/d̃)`. Then, any compression strategy for Game 1 that succeeds with probability
at least `ξ > 0` must satisfy `I(Message; E^(i) | E^(<i)) ≥ ξ · k d̃/(1 + log(√d/γ)) − log 2`."

**Formalization Note.** `C` is universal (chosen first). Information is `condMutualInfo` in nats;
the bound "`≥ Y` bits" is `ENNReal.ofReal (Y · ln 2) ≤ I` with log base 2 (p.7), so "`log 2`" is one bit.
The ratio conditions are written multiplied out (`γ/β ≥ X` as `Xβ ≤ γ`, `κ ≤ 1/(dΣ)` as `dΣκ ≤ 1`,
`δ ≤ 1/d` as `dδ ≤ 1`), which treats a zero denominator as `+∞`. `T` is invertible; the accuracies
are positive and nonincreasing (NoiseAddition's input, p.7); `1 ≤ i ≤ N`. Any compression strategy:
private encoder and decoder randomness, standard Borel message space (`IsGame1Play`). Success
probability is the measure of the winning event (`game1Win`). -/
theorem proposition_3 :
    ∃ C : ℝ, 0 < C ∧ ∀ (d dt k N i : ℕ) (T : Op d) (δ : ℕ → ℝ) (β γ η ξ : ℝ),
      IsUnit T → (∀ j ≤ N, 0 < δ j) → (∀ j < N, δ (j + 1) ≤ δ j) → 1 ≤ i → i ≤ N →
      (d : ℝ) * δ (i - 1) ≤ 1 → δ (i - 1) ≤ η →
      (d : ℝ) * (∑ j ∈ Finset.Icc i N, δ j) * condNum T ≤ 1 →
      C * k * (η / δ (i - 1)) * Real.sqrt (d / dt) * β ≤ γ → 0 < ξ →
      ∀ {Ω A B Mes : Type} [MeasurableSpace Ω] [MeasurableSpace A] [MeasurableSpace B]
        [MeasurableSpace Mes] [StandardBorelSpace Mes] [Nonempty Mes]
        (μ : Measure Ω) [IsProbabilityMeasure μ] (ν : Measure (Op d)) (E : Ω → Op d)
        (ch : ℕ → Ω → Op d) (Uenc : Ω → A) (Udec : Ω → B) (enc : (ℕ → Op d) × A → Mes)
        (dec : Mes × (ℕ → Op d) × B → (Fin k → Vec d)),
        IsGame1Play μ ν dt T δ N E ch Uenc Udec enc dec →
        ENNReal.ofReal ξ ≤
          μ {ω | game1Win β γ η i (fun j => ch j ω) (game1Output enc dec i ch Uenc Udec ω)} →
        ENNReal.ofReal
            ((ξ * ((k : ℝ) * dt) / (1 + Real.logb 2 (Real.sqrt d / γ)) - 1) * Real.log 2) ≤
          ThompsonTutorial.InfoRatio.condMutualInfo μ (game1Message enc i ch Uenc) (ch i)
            (fun ω => truncSeq i (fun j => ch j ω)) := by sorry

end MemQueryFeas
