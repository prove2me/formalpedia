-- Prove2me | Theorems.Thm_KMeansTaper_Supplement_theorem_5_7
-- name    : KMeansTaper.Supplement.theorem_5_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-18T06:32:59.180469+00:00
-- url     : https://prove2.me/theorems/c3c96f8f-3750-4003-9e59-0c419b4571e1
-- title:
--   Theorem 5.7 — randomized squared tapered rounding
-- statement:
--   Let $\kappa>0$ and $0<c\le1$, and assume $\mathrm{SFI}(\kappa,c)$. For every real $\tau\in(0,1]$, there is a threshold $\Delta_0$ such that for every integer $\Delta\ge\Delta_0$ there is a nonnegative additive constant $C(\tau,\Delta)$ and a randomized expected-polynomial algorithm with the following guarantee.
--
--   Given valid grid openings of total mass $M\ge1$, every halting run outputs a nonempty set $O$ of grid pieces satisfying
--
--   $$
--   |O|\le M+C(\tau,\Delta).
--   $$
--
--   Separately for every client $j$, expectation over the algorithm's fair random bits satisfies
--
--   $$
--   \mathbb E\bigl[d(j,O)^2\bigr]
--   \le \left(1+\frac{\kappa}{e}+\tau\right)V_{j,0},
--   $$
--
--   where $V_{j,0}$ is the squared cost of the client's initial nearest unit under the grid openings. The algorithm's finite machine has expected running time polynomial in the encoded input length; hence it halts almost surely.
--
--   **Formalization Note** The output uses the base mission's grid-piece representation and membership-mask encoding. The expectation is a measurable nonnegative lower integral in $\mathbb R_{\ge0}\cup\{+\infty\}$, preventing a nonintegrable random cost from receiving Lean's default Bochner-integral value zero. Positivity of $\kappa$ is the standing assumption of the coefficient setup in Section 2.
--
--   Differences from the source:
--   - encoding: the Section 2 standing assumption $\kappa>0$ is implicit in the theorem sentence → Lean states $\kappa>0$ explicitly; reason: standing assumptions must appear in the formal binders
--   - reading: a randomized expected-polynomial algorithm → a finite fair-coin multi-tape machine whose extended expected halting time is polynomial in the blank-safe encoding length; reason: the paper names no randomized machine model
--   - encoding: an output facility set $O$ under grid openings → a nonempty set of indices of the published grid-piece list, encoded by its membership mask; reason: this is the base mission's representation of co-located grid openings
--   - encoding: the source writes the distance to the algorithm's output without an empty-set case → every halting output is required to be nonempty; reason: this excludes the reused distance function's junk value zero at the empty set
--   - encoding: $\mathbb E[d(j,O)^2]$ → a measurable nonnegative lower integral over fair-coin streams; reason: the extended integral represents the same expectation and cannot default to zero on a nonintegrable function
--   - encoding: "all large $\Delta$" and $C(\tau,\Delta)$ → an explicit threshold $\Delta_0$, every natural $\Delta\ge\Delta_0$, and a nonnegative real $C$ chosen before the input; reason: this makes the source's eventual and uniform quantifiers explicit
-- source:
--   Zhu, A tight approximation for metric k-means via squared tapered rounding, STOC 2027 submission (manuscript sha256 8b6610229e43dc2441325b120437136afe762dbd6e873f73919fcb6b043fc5a3), Theorem 5.7 and proof, pp.12-13 (PDF pp.15-16)

import Mathlib
import Definitions.Def_MetricKMedian
import Definitions.Def_KMeansTaper_SFI
import Definitions.Def_KMeansTaper_unitCost
import Definitions.Def_KMeansTaper_encodePieces
import Definitions.Def_KMeansTaper_Supplement_IsExpectedPolyGridAlgorithm

namespace KMeansTaper
namespace Supplement

open OAI.MetricKMedian (Instance)
open IntQuotHNP.Supplement (MTMachine coinMeasure haltTime)
open MeasureTheory

/-- **Theorem 5.7 (tapered rounding, squared)**, p.12 (PDF p.15).

Zhu, *A tight approximation for metric k-means via squared tapered rounding*, STOC 2027
submission (manuscript sha256 8b6610229e43dc2441325b120437136afe762dbd6e873f73919fcb6b043fc5a3).

Assume `κ > 0`, `SFI(κ,c)`, and `0 < c ≤ 1`. For every real `τ ∈ (0,1]` and all
sufficiently large integer grids `Δ`, a randomized expected-polynomial algorithm maps every
valid grid opening of mass at least one to an output `O`. Almost surely,
`|O| ≤ M + C(τ,Δ)`; separately for every client `j`, its expected squared connection cost is
at most `(1 + κ/e + τ)V_{j,0}`.

**Formalization Note.** Positivity of `κ` is inherited from the coefficient setup at the start of
Section 2. "All large Δ" is `∃ Δ₀, ∀ Δ ≥ Δ₀`. Grid inputs, masses, `V_{j,0}` and
piece distances reuse the published base definitions. The algorithm is the fair-coin Las Vegas
machine tied to its almost-sure piece-set output by `IsExpectedPolyGridAlgorithm`; its expected
runtime bound forces almost-sure halting. The nonnegative expectation is a lower integral in
`ℝ≥0∞`, so nonintegrability cannot turn it into zero. -/
theorem theorem_5_7 (κ c : ℝ) (hκ : 0 < κ) (hc0 : 0 < c) (hc1 : c ≤ 1) (hSFI : SFI κ c)
    (τ : ℝ) (hτ0 : 0 < τ) (hτ1 : τ ≤ 1) :
    ∃ Δ₀ : ℕ, ∀ Δ : ℕ, Δ₀ ≤ Δ → ∃ C : ℝ, 0 ≤ C ∧
      ∃ (A : MTMachine)
        (out : (z : Σ _ : Instance, List (ℕ × ℕ)) → (ℕ → Bool) → Finset (Fin z.2.length)),
        IsExpectedPolyGridAlgorithm A out ∧
        ∀ (I : Instance) (L : List (ℕ × ℕ)), GridValid I Δ L → 1 ≤ gridMass Δ L →
          (∀ ω, haltTime A (encodeBoolWord (encodeGridInput ⟨I, L⟩)) ω < ⊤ →
            (out ⟨I, L⟩ ω).Nonempty ∧ ((out ⟨I, L⟩ ω).card : ℝ) ≤ gridMass Δ L + C) ∧
          ∀ j ∈ I.clients,
            Measurable (fun ω => pieceNearest I L j (out ⟨I, L⟩ ω) ^ 2) ∧
              ∫⁻ ω, ENNReal.ofReal (pieceNearest I L j (out ⟨I, L⟩ ω) ^ 2) ∂coinMeasure ≤
                ENNReal.ofReal ((1 + κ / Real.exp 1 + τ) * pieceUnitCost I Δ L j) := by sorry

end Supplement
end KMeansTaper
