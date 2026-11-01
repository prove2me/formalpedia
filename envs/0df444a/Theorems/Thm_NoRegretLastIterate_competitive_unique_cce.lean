-- Prove2me | Theorems.Thm_NoRegretLastIterate_competitive_unique_cce
-- name    : NoRegretLastIterate.competitive_unique_cce
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T13:32:04.210782+00:00
-- url     : https://prove2.me/theorems/cc7fb7b0-c757-4d37-8b0b-a7dd0582451c
-- title:
--   App. B, p.32 — a competitive game has the unique CCE $\mu=p^*\times q^*$
-- statement:
--   Let $(G,H)$ be a competitive $2\times2$ game with Nash equilibrium $(p^*,q^*)$ and let $\mu$ be a probability distribution on $\{0,1\}^2$.
--
--   1. $\mu$ satisfies, as printed on p.32,
--   $$
--   \mathbb E_{(I,J)\sim\mu}[G(I,J)]\le\mathbb E_{(I,J)\sim\mu}[G(i',J)]\quad\text{and}\quad\mathbb E_{(I,J)\sim\mu}[H(I,J)]\le\mathbb E_{(I,J)\sim\mu}[H(I,j')]
--   $$
--   for all $i',j'\in\{0,1\}$, if and only if $\mu=p^*\times q^*$.
--   2. $\mu$ is a coarse correlated equilibrium in the payoff convention (the same inequalities with $\ge$) if and only if $\mu=p^*\times q^*$.
--
--   The printed system uses the cost convention although $G,H$ are payoffs; it is the payoff-CCE system of the game $(-G,-H)$, which is again competitive and has the same interior equilibrium, so both clauses hold. Clause 2 is the form in which the uniqueness feeds the proof of Lemma 3.7: average play of two no-regret players is an approximate CCE, hence close to $p^*\times q^*$.
--
--   **Formalization Note** Distributions are $2\times2$ matrices satisfying the published `CalibratedCE.Convergence.IsJointDist`.
--
--   Differences from the source:
--   - generalization: unique µ satisfying the printed ≤ inequalities, µ = p∗ × q∗ → adds clause 2: the payoff-convention (≥) CCE is also unique and equal to p∗ × q∗; reason: an added true clause used by the proof of Lemma 3.7; clause 1 is the printed statement unchanged
--   - encoding: "there is a unique distribution µ … this distribution corresponds to the unique NE, µ = p∗ × q∗" → for a given NE (p∗, q∗) and every joint distribution D: D satisfies the system ↔ D = p∗ × q∗; reason: same content: the set of solutions is {p∗ × q∗}; the NE is unique (p.8)
--   - encoding: (p∗, q∗) a Nash equilibrium in mixed strategies; actions 0, 1 → published RankOneBimatrix.BinSearch.IsNE on the probability vectors (1 − p, p), (1 − q, q); actions Fin 2; reason: Lean convention and published vocabulary; same instances
-- source:
--   Muthukumar, Phade, Sahai, On the Impossibility of Convergence of Mixed Strategies with Optimal No-Regret Learning, arXiv:2012.02125v3, App. B, p.32 ("for any competitive game, there is a unique CCE … µ = p∗ × q∗")

import Mathlib
import Definitions.Def_RankOneBimatrix_BinSearch_Game
import Definitions.Def_CalibratedCE_Convergence_Game
import Definitions.Def_NoRegretLastIterate_Game

namespace NoRegretLastIterate

/-- Muthukumar, Phade, Sahai, arXiv:2012.02125v3, App. B, p.32: "for any competitive game, there
is a unique CCE, i.e. there is a unique distribution µ that satisfies
`E_{(I,J)∼µ}[G(I, J)] ≤ E_{(I,J)∼µ}[G(i′, J)]` for any unilateral deviation `i′ ∈ {0, 1}` of
player 1, and `E_{(I,J)∼µ}[H(I, J)] ≤ E_{(I,J)∼µ}[H(I, j′)]` for any unilateral deviation
`j′ ∈ {0, 1}` of player 2. In fact, this distribution corresponds to the unique NE of this game,
i.e. µ = p∗ × q∗." Stated for a competitive `(G, H)` with Nash equilibrium `(p∗, q∗)` and a joint
distribution `D`: (1) `D` satisfies the printed `≤` system iff `D = p∗ × q∗`; (2) `D` is a coarse
correlated equilibrium in the payoff convention (`≥`) iff `D = p∗ × q∗`.

**Formalization Note** Clause (1) is the page's system verbatim (cost-convention inequalities for
the payoffs `G`, `H`); clause (2) is the payoff-convention system `IsCCE`, added because the proof
of Lemma 3.7 uses it. Joint distributions use the published `CalibratedCE.Convergence.IsJointDist`;
Nash equilibrium is the published `RankOneBimatrix.BinSearch.IsNE`. -/
theorem competitive_unique_cce {G H : Matrix (Fin 2) (Fin 2) ℝ} (hcomp : IsCompetitive G H)
    {p q : ℝ} (hNE : RankOneBimatrix.BinSearch.IsNE G H (mix p) (mix q))
    (D : Fin 2 → Fin 2 → ℝ) (hD : CalibratedCE.Convergence.IsJointDist D) :
    (((∀ i' : Fin 2, ∑ i, ∑ j, D i j * G i j ≤ ∑ i, ∑ j, D i j * G i' j) ∧
        (∀ j' : Fin 2, ∑ i, ∑ j, D i j * H i j ≤ ∑ i, ∑ j, D i j * H i j')) ↔
        D = prodDist p q) ∧
      (IsCCE G H D ↔ D = prodDist p q) := by sorry

end NoRegretLastIterate
