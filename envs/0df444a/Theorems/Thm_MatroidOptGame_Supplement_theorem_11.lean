-- Prove2me | Theorems.Thm_MatroidOptGame_Supplement_theorem_11
-- name    : MatroidOptGame.Supplement.theorem_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T06:55:53.948143+00:00
-- url     : https://prove2.me/theorems/edc42156-4837-4dc8-a175-3412ff632c9d
-- title:
--   Theorem 11 — oracle upper bound on MAX: expected gain at most $1+2/n+n\,2^{-n/2}$ with $s\le 2^{n/2}$ queries
-- statement:
--   Fix $n\ge 4$. The game is the matroid base minimization game (MAX first; MAX deletes, MIN contracts and may not take a loop; MAX's payoff is $\infty$ if its deletions contain a cut, otherwise the weight of the base MIN secures). The hidden matroid $\widetilde{\mathcal M}=\mathcal M_{n,S_0,\pi}$ on $E_n=\{0,\dots,2n-1\}$ is drawn uniformly over the labels $(S_0,\pi)$, and the weights are $w(0)=w(1)=1$, $w(i)=0$ otherwise.
--
--   **Theorem 11.** There is a strategy for MIN, depending on $\widetilde{\mathcal M}$ and legal in every matroid of the family, such that every MAX who does not know $\widetilde{\mathcal M}$ and accesses it only through queries $\widetilde F_1,\dots,\widetilde F_s$ to the independence oracle $\widetilde{\mathcal O}$, with
--   $$
--   s\le 2^{n/2},
--   $$
--   has expected gain
--   $$
--   \mathbb E[\,p(c,s)\,]\;\le\;1+\frac 2n+n\cdot 2^{-n/2}.
--   $$
--   The queries may be adaptive, may be asked before the first move and between moves, and MAX may randomize; the expectation is over the hidden label and MAX's randomness.
--
--   By Lemma 9 the value of the game on every matroid of the family is at least $2$, so a MAX who knows the matroid gains $2$; with subexponentially many oracle queries MAX gains little more than $1$. This shows the factor-two guarantees of Theorem 1 cannot be improved for oracle-access players.
--
--   **Formalization Note** The family is any map $\ell\mapsto\widetilde{\mathcal M}_\ell$ on labels with ground set all of $E_n$ whose independent sets are those of `pairBaseIndep` (satisfiable by Lemma 8). MIN is a function of the matroid, chosen before $s$ and MAX. A randomized MAX is a `PMF` on deterministic oracle players, each within budget $s$ and legal in every matroid of the family. The payoff in $\mathbb N\cup\{\infty\}$ is read in $[0,\infty]$.
--
--   Differences from the source:
--   - generalization: for the given query-bounded MAX, "there exists a strategy for MIN (depending on M̃)" → ∃ σ : Matroid → Strategy, legal in every M̃ of the family, before ∀ s ∀ randomized MAX; reason: the proof's MIN (Lehman strategy, or smallest j0 then π(j0)/π(i0)) never looks at MAX; one MIN for all players implies one MIN for each player
--   - generalization: queries F̃1,…,F̃s with MAX's first move depending on them → adaptive queries at any of MAX's turns (before the first move and between moves), each depending on earlier answers and on MIN's moves, total ≤ s; reason: the proof allows queries after the first round ("we allow MAX to make the queries both before the first round and after the first round"); a bound against stronger MAX players specializes to the stated one
--   - reading: MAX's expected gain (MAX may randomize: "We fix MAX's random choices") → randomized MAX = PMF on deterministic oracle players; expectation over the uniform label and the PMF; reason: the proof averages over MAX's random choices; deterministic MAX is the point-mass case
--   - encoding: M̃ = M_{n,S0,π} drawn uniformly on the choice of S0, π (Lemma 8: a matroid) → a family Mh indexed by labels with (Mh ℓ).E = univ and independent sets given by pairBaseIndep, as hypotheses; average with weight 1/|labels|; reason: Lean has no proof-free constructor for these matroids; Lemma 8 makes the hypotheses satisfiable
--   - encoding: label (S0, bijection π : S0 → S1, π(0) = 1) → (S0, fixed-point-free involution exchanging S0 and S1, π(0) = 1); reason: restriction to S0 is a bijection of the two label sets, so the uniform laws agree
--   - encoding: MAX plays by the game's rules → each deterministic MAX in the support induces a LegalMax strategy in every matroid of the family; reason: the game's own rules (MAX plays unplayed elements)
--   - encoding: payoff in ℕ ∪ {∞}; expected gain → published payoff in ℕ∞, coerced to ℝ≥0∞ (∞ ↦ ⊤); bound as ENNReal.ofReal of the real number 1 + 2/n + n·2^(−n/2); reason: Lean convention; the bound is positive, so no truncation
-- source:
--   Jahn–Koolyk–Ostrovsky–Rabani–Schulman, Approximation and Hardness in Optimization Games, STOC 2027 submission (manuscript sha256 7ad38b1a…dee74), Section 2.2.1, Theorem 11, p.13 (family p.11, law p.12)

import Mathlib
import Definitions.Def_MatroidOptGame_Strategy
import Definitions.Def_MatroidOptGame_LegalMax
import Definitions.Def_MatroidOptGame_LegalMin
import Definitions.Def_MatroidOptGame_payoff
import Definitions.Def_MatroidOptGame_Supplement_heavyWeight
import Definitions.Def_MatroidOptGame_Supplement_pairBaseIndep
import Definitions.Def_MatroidOptGame_Supplement_PairLabel
import Definitions.Def_MatroidOptGame_Supplement_OraclePlayer
import Definitions.Def_MatroidOptGame_Supplement_WithinBudget
import Definitions.Def_MatroidOptGame_Supplement_oracleStrategy

open scoped ENNReal

namespace MatroidOptGame.Supplement

/-- **Theorem 11 (oracle upper bound on MAX's payoff).** Let `n ≥ 4` and let the hidden matroid
`M̃ = M_{n,S₀,π}` on `E_n = Fin (2n)` be drawn uniformly over the labels `(S₀, π)`, with weights
`w(0) = w(1) = 1` and `0` elsewhere. There is a MIN strategy, depending on `M̃` and legal in every
`M̃` of the family, such that every randomized adaptive MAX that reaches `M̃` only through at most
`s ≤ 2^{n/2}` independence queries in total (and plays legally in every `M̃` of the family) has
expected payoff at most `1 + 2/n + n·2^{−n/2}`.

Source: Jahn–Koolyk–Ostrovsky–Rabani–Schulman, *Approximation and Hardness in Optimization Games*,
STOC 2027 submission (manuscript sha256 7ad38b1a…dee74), Section 2.2.1, Theorem 11, p.13; the family on p.11, its law on p.12.

**Formalization Note.** The family is any `Mh` indexed by the labels whose independent sets are
those of `Supplement.pairBaseIndep` (Lemma 8 of the paper says such matroids exist, so the
hypotheses are satisfiable). MIN is a function `σ` of the matroid, chosen before the budget and
the player. A randomized MAX is a `PMF` on deterministic oracle players; its strategy in `M̃` is
`Supplement.oracleStrategy (M̃) P 0 s`. The expectation is over the uniform label and the player's
law, of the published payoff `p(c, s) ∈ ℕ∞` read in `ℝ≥0∞` (`∞ ↦ ⊤`). -/
theorem theorem_11 (n : ℕ) (hn : 4 ≤ n)
    (Mh : PairLabel n → Matroid (Fin (2 * n)))
    (hE : ∀ ℓ, (Mh ℓ).E = Set.univ)
    (hI : ∀ ℓ (S : Finset (Fin (2 * n))),
      (Mh ℓ).Indep (S : Set (Fin (2 * n))) ↔ pairBaseIndep n ℓ.1.1 ℓ.1.2 S) :
    ∃ σ : Matroid (Fin (2 * n)) → Strategy (Fin (2 * n)),
      (∀ ℓ, LegalMin (Mh ℓ) (σ (Mh ℓ))) ∧
      ∀ s : ℕ, (s : ℝ) ≤ (2 : ℝ) ^ ((n : ℝ) / 2) →
      ∀ μ : PMF (OraclePlayer (Fin (2 * n))),
        (∀ P ∈ μ.support, WithinBudget s P ∧
          ∀ ℓ, LegalMax (Mh ℓ) (oracleStrategy (Mh ℓ) P 0 s)) →
        (Fintype.card (PairLabel n) : ℝ≥0∞)⁻¹ *
            ∑ ℓ : PairLabel n, ∑' P : OraclePlayer (Fin (2 * n)),
              μ P * ((payoff (Mh ℓ) heavyWeight
                (oracleStrategy (Mh ℓ) P 0 s) (σ (Mh ℓ)) : ℕ∞) : ℝ≥0∞) ≤
          ENNReal.ofReal (1 + 2 / (n : ℝ) + (n : ℝ) * (2 : ℝ) ^ (-(n : ℝ) / 2)) := by sorry

end MatroidOptGame.Supplement
