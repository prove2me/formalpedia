-- Prove2me | Theorems.Thm_MatroidOptGame_Supplement_theorem_14
-- name    : MatroidOptGame.Supplement.theorem_14
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T06:56:45.766858+00:00
-- url     : https://prove2.me/theorems/c2aa64c7-c4c7-4811-8fd7-3428d2cb5cb4
-- title:
--   Theorem 14 — oracle lower bound on MIN: expected cost at least $2-2^{-n/3+2}$ with $s\le 2^{n/3}$ queries
-- statement:
--   Fix an even $n\ge 4$. The game is the matroid base minimization game (MAX first; MAX deletes, MIN contracts and may not take a loop; MAX's payoff, MIN's cost, is $\infty$ if MAX's deletions contain a cut, otherwise the weight of the base MIN secures). The hidden matroid is $\widetilde{\mathcal M}=\mathcal M_{n,H}$ on $E_n=\{0,\dots,2n-1\}$, where $H$ is drawn uniformly at random from the odd transversals of the pairs $\{2i,2i+1\}$, and the weights are $w(0)=w(1)=1$, $w(i)=0$ otherwise.
--
--   **Theorem 14.** There is a strategy for MAX, depending on $\widetilde{\mathcal M}$ and legal in every matroid of the family, such that every MIN who does not know $\widetilde{\mathcal M}$ and makes at most
--   $$
--   s\le 2^{n/3}
--   $$
--   independence queries has expected cost
--   $$
--   \mathbb E[\,p(c,s)\,]\;\ge\;2-2^{-n/3+2}.
--   $$
--   The queries may be adaptive and asked at any of MIN's turns, MIN may randomize, and MIN must play legally in whichever matroid of the family is hidden; the expectation is over $H$ and MIN's randomness.
--
--   By Lemma 13 the value of the game on every $\mathcal M_{n,H}$ is $1$, so a MIN who knows the matroid pays $1$; with subexponentially many queries MIN pays nearly $2$. Together with Theorem 11 this shows the factor-two guarantees of Theorem 1 are tight for oracle-access players.
--
--   **Formalization Note** The family is any map $H\mapsto\widetilde{\mathcal M}_H$ with ground set all of $E_n$ whose independent sets are those of `oddTransversalIndep` (satisfiable by Lemma 12). MAX is a function of the matroid, chosen before $s$ and MIN. A randomized MIN is a `PMF` on deterministic oracle players, each within budget $s$ and legal in every matroid of the family. The payoff in $\mathbb N\cup\{\infty\}$ is read in $[0,\infty]$.
--
--   Differences from the source:
--   - generalization: for the given query-bounded MIN, "there exists a strategy for MAX (depending on M̃)" → ∃ τ : Matroid → Strategy, legal in every M̃ of the family, before ∀ s ∀ randomized MIN; reason: the proof's MAX chooses by "a fixed rule independent of H" and partners of MIN's moves, never looking at MIN's coins; one MAX for all players implies one for each
--   - reading: "can generate at most s independence queries" → adaptive queries at any of MIN's turns (between moves included), each depending on earlier answers and MAX's moves, total over the game ≤ s; reason: the proof: "Answer queries of MIN as needed, including between moves"
--   - reading: MIN's expected cost ("Fix MIN's random choices … averaging over MIN's random choices") → randomized MIN = PMF on deterministic oracle players; expectation over the uniform H and the PMF; reason: the proof averages over MIN's random choices; deterministic MIN is the point-mass case
--   - encoding: M̃ = M_{n,H}, H uniform over the odd transversals (Lemma 12: a matroid) → a family Mh indexed by odd transversals with (Mh H).E = univ and independent sets given by oddTransversalIndep, as hypotheses; average with weight 1/|odd transversals|; reason: Lean has no proof-free constructor for these matroids; Lemma 12 makes the hypotheses satisfiable
--   - encoding: MIN may not select a loop (game rules) → each deterministic MIN in the support induces a LegalMin strategy in every matroid of the family; reason: the game's rules apply in whichever matroid is hidden
--   - encoding: payoff in ℕ ∪ {∞}; expected cost → published payoff in ℕ∞, coerced to ℝ≥0∞ (∞ ↦ ⊤); bound ENNReal.ofReal(2 − 2^(−n/3+2)) ≤ expectation; reason: Lean convention; for n ≥ 4 the bound is positive, so no truncation
-- source:
--   Jahn–Koolyk–Ostrovsky–Rabani–Schulman, Approximation and Hardness in Optimization Games, STOC 2027 submission (manuscript sha256 7ad38b1a…dee74), Section 2.2.2, Theorem 14, p.15 (family p.14)

import Mathlib
import Definitions.Def_MatroidOptGame_Strategy
import Definitions.Def_MatroidOptGame_LegalMax
import Definitions.Def_MatroidOptGame_LegalMin
import Definitions.Def_MatroidOptGame_payoff
import Definitions.Def_MatroidOptGame_Supplement_heavyWeight
import Definitions.Def_MatroidOptGame_Supplement_OddTransversal
import Definitions.Def_MatroidOptGame_Supplement_oddTransversalIndep
import Definitions.Def_MatroidOptGame_Supplement_OraclePlayer
import Definitions.Def_MatroidOptGame_Supplement_WithinBudget
import Definitions.Def_MatroidOptGame_Supplement_oracleStrategy

open scoped ENNReal

namespace MatroidOptGame.Supplement

/-- **Theorem 14 (oracle lower bound on MIN's cost).** Let `n ≥ 4` be even and let the hidden
matroid `M̃ = M_{n,H}` on `E_n = Fin (2n)` have `H` drawn uniformly from the odd transversals of
the pairs `{2i, 2i+1}`, with weights `w(0) = w(1) = 1` and `0` elsewhere. There is a MAX strategy,
depending on `M̃` and legal in every `M̃` of the family, such that every randomized adaptive MIN
that reaches `M̃` only through at most `s ≤ 2^{n/3}` independence queries in total (and plays
legally in every `M̃` of the family) has expected cost at least `2 − 2^{−n/3+2}`.

Source: Jahn–Koolyk–Ostrovsky–Rabani–Schulman, *Approximation and Hardness in Optimization Games*,
STOC 2027 submission (manuscript sha256 7ad38b1a…dee74), Section 2.2.2, Theorem 14, p.15; the family on p.14, its law on p.15.

**Formalization Note.** The family is any `Mh` indexed by the odd transversals whose independent
sets are those of `Supplement.oddTransversalIndep` (Lemma 12 of the paper says such matroids
exist). MAX is a function `τ` of the matroid, chosen before the budget and the player. A
randomized MIN is a `PMF` on deterministic oracle players; its strategy in `M̃` is
`Supplement.oracleStrategy (M̃) P 1 s`, required legal (moves keep MIN's set independent) in every
`M̃` of the family. The expectation is over the uniform `H` and the player's law, of the published
payoff `p(c, s) ∈ ℕ∞` read in `ℝ≥0∞` (`∞ ↦ ⊤`). -/
theorem theorem_14 (n : ℕ) (hn : 4 ≤ n) (hev : Even n)
    (Mh : OddTransversal n → Matroid (Fin (2 * n)))
    (hE : ∀ H, (Mh H).E = Set.univ)
    (hI : ∀ H (S : Finset (Fin (2 * n))),
      (Mh H).Indep (S : Set (Fin (2 * n))) ↔ oddTransversalIndep n H.1 S) :
    ∃ τ : Matroid (Fin (2 * n)) → Strategy (Fin (2 * n)),
      (∀ H, LegalMax (Mh H) (τ (Mh H))) ∧
      ∀ s : ℕ, (s : ℝ) ≤ (2 : ℝ) ^ ((n : ℝ) / 3) →
      ∀ μ : PMF (OraclePlayer (Fin (2 * n))),
        (∀ P ∈ μ.support, WithinBudget s P ∧
          ∀ H, LegalMin (Mh H) (oracleStrategy (Mh H) P 1 s)) →
        ENNReal.ofReal (2 - (2 : ℝ) ^ (-(n : ℝ) / 3 + 2)) ≤
          (Fintype.card (OddTransversal n) : ℝ≥0∞)⁻¹ *
            ∑ H : OddTransversal n, ∑' P : OraclePlayer (Fin (2 * n)),
              μ P * ((payoff (Mh H) heavyWeight
                (τ (Mh H)) (oracleStrategy (Mh H) P 1 s) : ℕ∞) : ℝ≥0∞) := by sorry

end MatroidOptGame.Supplement
