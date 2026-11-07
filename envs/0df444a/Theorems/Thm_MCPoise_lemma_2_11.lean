-- Prove2me | Theorems.Thm_MCPoise_lemma_2_11
-- name    : MCPoise.lemma_2_11
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:34:53.015033+00:00
-- url     : https://prove2.me/theorems/9f516af0-8d3a-4a45-984c-8d4ac3c4fcbd
-- title:
--   Lemma 2.11 — simultaneous rounding: one path per label with degree at most $8(L_\Delta + L'_d)$
-- statement:
--   Let the labels $(j, t)$ carry path lists $Q^t_j$ with rational weights $y^{j,t}_p \ge 0$ of sum $1$, with each path of length at most $4L'_d$, and suppose that
--   $$\sum_{j,t} \sum_{p \in Q^t_j} y^{j,t}_p\, |\delta(v) \cap E(p)| \le 8 L_\Delta \quad \text{for every vertex } v,$$
--   which is display (2) of Lemma 2.10.
--
--   **Lemma 2.11.** One can choose one path $P_{j,t} \in Q^t_j$ for each label so that the union $H$ of the chosen paths has maximum degree at most $8(L_\Delta + L'_d)$. Every chosen path has length at most $4L'_d$. The algorithm runs in time polynomial in the encoding length of the path sets and weights.
--
--   **Formalization Note** The degree is of the union as a set of edges, and the algorithm does not read $L_\Delta$.
--
--   Differences from the source:
--   - generalization: the path sets and weights constructed in Stage 1 → any weighted lists with these properties; reason: the proof (pp.36–37) reads only these properties, and Stage 1 gives them
--   - reading: an efficient, polynomial-time algorithm → one deterministic machine `Turing.TM2ComputableInPolyTime`, polynomial in a fixed binary encoding on every input; reason: the source names no machine, and every step it describes is deterministic
--   - encoding: labels (j, t), j ∈ [µ], t ∈ S′_j → positions in a list of labels; reason: the rounding does not read j or t
--   - encoding: parameter L_∆ → 0 ≤ L_∆ is a hypothesis; reason: display (2) implies it unless V is empty, where a negative value has no meaning
-- source:
--   R. Jain, A. Niaparast, R. Ravi, Polylog Pairwise Poise: Approximating Multicommodity Multicast, STOC 2027 submission (manuscript sha256 2c6a7cc5…), Lemma 2.11, p.19; proof, pp.36–37

import Mathlib
import Definitions.Def_MCPoise_maxDeg
import Definitions.Def_MCPoise_RoundIn

namespace MCPoise

/-- **Lemma 2.11 (simultaneous rounding).**
Jain, Niaparast, Ravi, *Polylog Pairwise Poise: Approximating Multicommodity Multicast*, STOC 2027 submission (manuscript sha256 2c6a7cc5…), Lemma 2.11, p.19: "Given the path sets Q^t_j and fractional weights y^{j,t}_p constructed in Stage 1, we can choose one path P_{j,t} ∈ Q^t_j for every j ∈ [µ] and
t ∈ S′_j such that the subgraph H := ∪_{j∈[µ]} ∪_{t∈S′_j} P_{j,t} has maximum degree at most 8(L_∆ + L′_d). Every chosen path has length at most 4L′_d. The algorithm runs in
time polynomial in the encoding length of the path sets and their fractional weights."

The hypotheses are what the proof (pp.36–37) reads from Stage 1: for each label, the weights are nonnegative with sum `1` and each path has at most `4L′_d` edges; and display (2)
holds with `L_∆`. One machine outputs one index per label; `L_∆` is quantified after the output, since the machine does not read it.

**Formalization Note.** The degree is of the union as a set of edges, so a shared edge counts once (`pathsGraph`). `Σ_{e∈δ(v)} Σ_{p∋e}` of display (2) is `Σ_p y_p |δ(v) ∩ E(p)|`, as on p.36. `0 ≤ L_∆` follows
from display (2) unless `V` is empty. -/
theorem lemma_2_11 :
    ∃ alg : RoundIn → List ℕ, Nonempty (Turing.TM2ComputableInPolyTime encRoundIn encIdx alg) ∧
      ∀ (R : RoundIn) (LΔ : ℝ), 0 ≤ LΔ →
        (∀ l ∈ R.labels, (∀ a ∈ l, 0 ≤ a.2 ∧ (pEdges a.1).length ≤ 4 * R.Lp) ∧
          (l.map fun a => (a.2 : ℝ)).sum = 1) →
        (∀ v : Fin R.n, (R.labels.map fun l =>
          (l.map fun a => (a.2 : ℝ) * (pInc v a.1 : ℝ)).sum).sum ≤ 8 * LΔ) →
        (alg R).length = R.labels.length ∧
        (∀ l, l < R.labels.length → (alg R).getD l 0 < (R.labels.getD l []).length) ∧
        (maxDeg (pathsGraph ((List.range R.labels.length).map (R.chosen (alg R)))) : ℝ) ≤
          8 * (LΔ + (R.Lp : ℝ)) ∧
        ∀ l, l < R.labels.length → (pEdges (R.chosen (alg R) l)).length ≤ 4 * R.Lp := by sorry

end MCPoise
