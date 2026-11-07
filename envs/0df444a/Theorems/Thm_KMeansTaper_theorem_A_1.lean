-- Prove2me | Theorems.Thm_KMeansTaper_theorem_A_1
-- name    : KMeansTaper.theorem_A_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T17:06:40.947284+00:00
-- url     : https://prove2.me/theorems/c8b719ab-1c44-4c7b-bd3f-e0c01114ce84
-- title:
--   Theorem A.1 — deterministic grid preparation
-- statement:
--   For every rational $\eta>0$ there is $\Delta_0$ such that for every even $\Delta\ge\Delta_0$, with $g=1/\Delta$, there is a deterministic algorithm, a Turing machine (`Turing.TM2ComputableInPolyTime`, every tape alphabet finite) running in time polynomial in the input length, with the following property. Given an instance with a nonempty client set and rational openings $y$ with $0\le y_i\le1$, $y_i=0$ off $F$ and $\sum_iy_i\ge1$, with squared nearest-unit costs $V_j$, it outputs openings $\tilde y_p\in g\mathbb Z\cap[0,1]$ on co-located labeled pieces at candidate facilities with
--
--   $$1\le\sum_p\tilde y_p\le\sum_iy_i+3g\qquad\text{and}\qquad\sum_{j\in J}\tilde V_j\le(1+\eta)\sum_{j\in J}V_j,$$
--
--   where $\tilde V_j$ is the squared nearest-unit cost of client $j$ for $\tilde y$.
--
--   This puts LP openings on a grid at a loss $1+\eta$ in cost and $3g$ in mass, which the rounding of Theorem D.17 requires.
--
--   **Formalization Note** The input is the published instance code followed by $y$; the output is a list of pieces $(\ell_p,Y_p)$ with $\tilde y_p=Y_p/\Delta$.
--
--   Differences from the source:
--   - encoding: Algorithm P (§A.3) is deterministic and runs in polynomial time (Lemma A.18) → there is a Turing.TM2ComputableInPolyTime machine with finite alphabets over encodeOpenings with output encodePieces; reason: the statement asserts a deterministic polynomial-time algorithm; Corollary A.17 uses only that
--   - reading: feasible rational openings y → rational y with 0 ≤ y_i ≤ 1, y_i = 0 off F and ∑ y_i ≥ 1; reason: the paper does not define 'feasible' for openings alone; these are the conditions under which the costs V_j are defined, and LP-feasible openings satisfy them
--   - encoding: openings on polynomially many co-located labeled pieces → a list of pairs (loc, Y) with Y ≤ Δ at candidate facilities (GridValid); reason: the number of pieces is bounded by the running time
--   - encoding: squared nearest-unit costs V_j, Ṽ_j → unitCost and pieceUnitCost, fractional-knapsack infima; reason: the greedy nearest unit is the knapsack optimum
-- source:
--   Zhu, A tight approximation for metric k-means via squared tapered rounding, STOC 2027 submission (manuscript sha256 8b6610229e43dc2441325b120437136afe762dbd6e873f73919fcb6b043fc5a3), Theorem A.1, p.20 (PDF p.23)

import Mathlib
import Definitions.Def_MetricKMedian
import Definitions.Def_KMeansTaper_unitCost
import Definitions.Def_KMeansTaper_encodePieces

namespace KMeansTaper

open OAI.MetricKMedian (Instance)

/-- **Theorem A.1 (deterministic grid preparation)**, p.20 (PDF p.23).

Zhu, *A tight approximation for metric k-means via squared tapered rounding*, STOC 2027
submission (manuscript sha256 8b6610229e43dc2441325b120437136afe762dbd6e873f73919fcb6b043fc5a3).

For every rational `η > 0` there is `Δ₀` such that for every even `Δ ≥ Δ₀`, `g = 1/Δ`, a
deterministic polynomial-time algorithm, given a nonempty client set and feasible rational
openings `y` with squared nearest-unit costs `V_j`, outputs openings `ỹ ∈ gℤ ∩ [0, 1]` on
co-located labeled pieces with `1 ≤ ∑ ỹ ≤ ∑ y + 3g` and `∑_j Ṽ_j ≤ (1 + η) ∑_j V_j`.

**Formalization Note.** "Algorithm P is deterministic, runs in polynomial time" is read as the
existence of a `Turing.TM2ComputableInPolyTime` machine with finite alphabets, over the published
`encodeInstance` followed by the openings in `encodeRat`; the output is a list of pieces
`(loc, Y)` (opening `Y/Δ` at facility `loc`) in `encodeNat`. "Feasible" openings are read as
`0 ≤ y_i ≤ 1`, `y_i = 0` off `F`, `∑ y_i ≥ 1`. "Polynomially many pieces" follows from the
time bound. -/
theorem theorem_A_1 (η : ℚ) (hη : 0 < η) :
    ∃ Δ₀ : ℕ, ∀ Δ : ℕ, Δ₀ ≤ Δ → Even Δ →
      ∃ (alg : (Σ I : Instance, (Fin I.n → ℚ)) → List (ℕ × ℕ))
        (M : Turing.TM2ComputableInPolyTime encodeOpenings encodePieces alg),
        (∀ k : M.tm.K, Finite (M.tm.Γ k)) ∧
        ∀ (I : Instance) (y : Fin I.n → ℚ), I.clients.Nonempty →
          (∀ i, 0 ≤ y i ∧ y i ≤ 1) → (∀ i, i ∉ I.facilities → y i = 0) → 1 ≤ ∑ i, y i →
          GridValid I Δ (alg ⟨I, y⟩) ∧ 1 ≤ gridMass Δ (alg ⟨I, y⟩) ∧
            gridMass Δ (alg ⟨I, y⟩) ≤ ∑ i, (y i : ℝ) + 3 / Δ ∧
            ∑ j ∈ I.clients, pieceUnitCost I Δ (alg ⟨I, y⟩) j
              ≤ (1 + η) * ∑ j ∈ I.clients, unitCost I (fun i => (y i : ℝ)) j := by sorry

end KMeansTaper
