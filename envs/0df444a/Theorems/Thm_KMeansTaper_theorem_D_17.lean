-- Prove2me | Theorems.Thm_KMeansTaper_theorem_D_17
-- name    : KMeansTaper.theorem_D_17
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T17:06:40.303256+00:00
-- url     : https://prove2.me/theorems/c4f3017c-9023-4443-9abf-68b6b38a1331
-- title:
--   Theorem D.17 — deterministic rounding
-- statement:
--   Assume $\mathrm{SFI}(\kappa,c)$ with rational $\kappa>0$ and real $0<c\le1$. For every rational $\tau\in(0,1]$ there is $\Delta_0$ such that for every $\Delta\ge\Delta_0$ there are a constant $C$ and a deterministic algorithm, a Turing machine (`Turing.TM2ComputableInPolyTime`, every tape alphabet finite) running in time polynomial in the input length, which, given an instance and grid openings on pieces (grid $1/\Delta$) of mass $M\ge1$, outputs a nonempty set $O$ of pieces with $|O|\le M+C$ and
--
--   $$\sum_{j\in J}d(j,O)^2\le\Bigl(1+\frac{\kappa}{e}+\frac34\tau\Bigr)\sum_{j\in J}V_{j,0},$$
--
--   where $V_{j,0}$ is the cost of client $j$'s nearest $\Delta$ copies of mass $1/\Delta$.
--
--   This is the derandomized squared tapered rounding: under SFI it opens a constant number of extra facilities and loses only $\kappa/e$ against the fractional cost.
--
--   **Formalization Note** The paper's constant is $4T\Delta/b^*$, fixed by $\tau$ and $\Delta$; here it is a natural number $C$ chosen after $\Delta$. The output is the indicator list of $O$ over the pieces.
--
--   Differences from the source:
--   - reading: "with rational κ > 0 and 0 < c ≤ 1" → κ : ℚ, c : ℝ; reason: the adjective "rational" qualifies κ only; the algorithm uses rational tapers within ζ of cP(x) (§5.2, (4)), so c need not be rational; this is the more general reading
--   - encoding: a deterministic algorithm whose running time is polynomial in the input length → a Turing.TM2ComputableInPolyTime machine with finite alphabets over encodeGridInput, identity output encoding; reason: Lean model of deterministic polynomial time
--   - encoding: |O| ≤ M + 4TΔ/b* with rational parameters → ∃ C : ℕ after Δ with |O| ≤ M + C; reason: 4TΔ/b* depends only on τ and Δ; rounding it up gives C
--   - encoding: outputs O (a set of opened copies) → a nonempty set of pieces, as an indicator list; reason: copies at one piece are co-located, so opened locations are counted; d(j, ∅) is undefined in the paper
--   - encoding: V_{j,0} (nearest Δ copies) → pieceUnitCost; reason: the knapsack optimum over pieces equals the cost of the nearest Δ copies
-- source:
--   Zhu, A tight approximation for metric k-means via squared tapered rounding, STOC 2027 submission (manuscript sha256 8b6610229e43dc2441325b120437136afe762dbd6e873f73919fcb6b043fc5a3), Theorem D.17, p.40 (PDF p.43)

import Mathlib
import Definitions.Def_MetricKMedian
import Definitions.Def_KMeansTaper_SFI
import Definitions.Def_KMeansTaper_unitCost
import Definitions.Def_KMeansTaper_encodePieces

namespace KMeansTaper

open OAI.MetricKMedian (Instance)

/-- **Theorem D.17 (deterministic rounding)**, p.40 (PDF p.43).

Zhu, *A tight approximation for metric k-means via squared tapered rounding*, STOC 2027
submission (manuscript sha256 8b6610229e43dc2441325b120437136afe762dbd6e873f73919fcb6b043fc5a3).

Assume `SFI(κ, c)` with rational `κ > 0` and `0 < c ≤ 1`. For every rational `τ ∈ (0, 1]`
and all large `Δ` there are rational parameters such that a deterministic algorithm, given grid
openings of mass `M ≥ 1`, outputs `O` with `|O| ≤ M + 4TΔ/b*` and
`∑_j d(j, O)² ≤ (1 + κ/e + (3/4)τ) ∑_j V_{j,0}`, in time polynomial in the input length.

**Formalization Note.** `κ` is rational as printed; the taper constant `c` is real (the page
qualifies only `κ` as rational, and the algorithm uses rational tapers `λ̂` within `ζ` of `cP(x)`,
§5.2 (4), p.10). The constant `4TΔ/b*` (which depends only on `τ` and `Δ`) is an
existential natural number `C` chosen after `Δ`. The algorithm is a
`Turing.TM2ComputableInPolyTime` machine with finite alphabets on `encodeInstance` followed by
the pieces; it returns the indicator bit-list of a nonempty set `O` of pieces (copies at one
piece are co-located, so a set of pieces counts opened locations). `V_{j,0}`, the cost of
`j`'s nearest `Δ` copies of mass `g`, is `pieceUnitCost`. -/
theorem theorem_D_17 (κ : ℚ) (c : ℝ) (hκ : 0 < κ) (hc0 : 0 < c) (hc1 : c ≤ 1) (hSFI : SFI κ c)
    (τ : ℚ) (hτ0 : 0 < τ) (hτ1 : τ ≤ 1) :
    ∃ Δ₀ : ℕ, ∀ Δ : ℕ, Δ₀ ≤ Δ → ∃ C : ℕ,
      ∃ (alg : (Σ _ : Instance, List (ℕ × ℕ)) → List Bool)
        (M : Turing.TM2ComputableInPolyTime encodeGridInput id alg),
        (∀ k : M.tm.K, Finite (M.tm.Γ k)) ∧
        ∀ (I : Instance) (L : List (ℕ × ℕ)), GridValid I Δ L → 1 ≤ gridMass Δ L →
          ∃ O : Finset (Fin L.length),
            alg ⟨I, L⟩ = List.ofFn (fun p : Fin L.length => decide (p ∈ O)) ∧ O.Nonempty ∧
            (O.card : ℝ) ≤ gridMass Δ L + C ∧
            ∑ j ∈ I.clients, pieceNearest I L j O ^ 2
              ≤ (1 + κ / Real.exp 1 + 3 / 4 * τ) * ∑ j ∈ I.clients, pieceUnitCost I Δ L j := by sorry

end KMeansTaper
