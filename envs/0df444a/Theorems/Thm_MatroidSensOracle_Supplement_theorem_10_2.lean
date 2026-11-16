-- Prove2me | Theorems.Thm_MatroidSensOracle_Supplement_theorem_10_2
-- name    : MatroidSensOracle.Supplement.theorem_10_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T03:27:13.059237+00:00
-- url     : https://prove2.me/theorems/8d243466-24c0-428d-8b5c-b063813cf632
-- title:
--   Theorem 10.2 (space lower bound $\Omega(\min((m^\star)^2,n^2))$ for colorful spanning tree oracles under $f=2$)
-- statement:
--   For every error level $\delta\in[0,1/2)$ there are constants $c,c_1>0$ and $C$ such that for all positive integers $n,m^\star$ with $4\le m^\star\le n(n-1)$ the following holds. There are a coloring $\chi$ of the vertex pairs of $V=\{0,\dots,n-1\}$ with $n-1$ colors, a susceptible set $E_Q$ with $c_1m^\star\le|E_Q|\le Cm^\star$, a set $T^*$ of $n-1$ pairs, and a class $\mathcal G$ of undirected graphs on $V$ such that every member contains $T^*$ as a colorful spanning tree and all members meet $E_Q$ in the same set $E_1$, with the following property. Every subset sensitivity oracle that answers, for every member and every query of at most two colored updates confined to $E_Q$ (insertion of a pair of $E_Q\setminus E_1$ with any color, deletion of a pair of $E_1$, or a color change of a pair of $E_1$), whether the updated graph has a colorful spanning tree, correctly with probability at least $1-\delta$, stores at least
--   $$c\cdot\min\{(m^\star)^2,n^2\}$$
--   bits on some member of $\mathcal G$.
--
--   This shows that the subset colorful spanning tree oracle of Theorem 9.9 has nearly optimal space for constant $f$.
--
--   Differences from the source:
--   - reading: there exists a graph G (and E_Q) such that any oracle requires Ω(·) bits → there is a class 𝒢 of graphs sharing V, the designated vertices and E_Q such that every oracle correct on all of 𝒢 stores at least c·min((m★)², n²) bits on some member; reason: for a single fixed graph an oracle needs no space; the proof's family indexed by a p × p matrix is what the theorem asserts
--   - generalization: subset sensitivity oracles (deterministic answers in the proof's counting argument) → information-theoretic randomized oracles (arbitrary measurable maps, no time bound) erring with probability at most δ per query, for every δ ∈ [0, 1/2), c depending on δ; reason: δ = 0 is the deterministic case of the proof; the paper's oracles are Monte Carlo
--   - encoding: f = 2 updates → queries U ⊆ E_Q with |U| ≤ 2; reason: the oracle supports at most two updates
--   - reading: a base spanning tree T∗ → a common (n − 1)-edge set T∗ contained in every member and forming a colorful spanning tree of it; reason: the construction's T∗ uses every color once; the colorful reading is the stronger one
--   - reading: updates of a colored subset oracle → at most two updates on pairs of E_Q: insertions with any color, deletions, color changes; reason: the proof's query inserts (x_i, t) with color p + j; §9.4.3: 'edges whose presence, cost, or color can change'
--   - reading: |E_Q| = Θ(m★) → c₁·m★ ≤ |E_Q| ≤ C·m★; reason: Θ with constants independent of n and m★
--   - encoding: an n-vertex edge-colored graph → undirected graphs on Fin n (edges (a, b), a < b) with a coloring χ : V × V → Fin (n − 1); reason: the §6.3 model of colored graphs
-- source:
--   Choudhary, Kumar, Saggi, Sensitivity Oracles for Matroid Packing, Matroid Covering, and Matching Problems with Applications, arXiv:2609.01283 (held version, sha256 0de50841…), Theorem 10.2, p.55 (PDF p.58)

import Mathlib
import Definitions.Def_MatroidSensOracle_Supplement_OracleModels

set_option autoImplicit false

namespace MatroidSensOracle.Supplement

open Classical in
/-- **Theorem 10.2 (space lower bound: colorful spanning trees).** Choudhary, Kumar, Saggi,
arXiv:2609.01283 (held version, sha256 0de50841…), p.55 (PDF p.58): "Let n, m★ be positive integers
with 4 ⩽ m★ ⩽ n(n−1). There exists an n-vertex edge-colored graph carrying a base spanning tree T∗
and a susceptible set E_Q of size Θ(m★) such that any subset sensitivity oracle for colorful spanning
tree requires Ω(min((m★)², n²)) bits of space under f = 2 updates."

**Formalization Note.**
* As in `theorem_10_1`, "a graph" is read as the family of the proof (pp.55–57): a class `𝒢` of
  undirected graphs on `Fin n` (edges `(a, b)`, `a < b`) with one colouring `χ : V × V → Fin (n − 1)`
  (exactly `n − 1` colour classes) and one susceptible set `E_Q` (pairs `a < b`), with
  `c₁ m★ ≤ |E_Q| ≤ C m★`; all members meet `E_Q` in the same set `E₁`, and all contain the same
  `(n − 1)`-edge set `T∗`, which is a colorful spanning tree of each member.
* Queries (§9.4.3, and the proof on p.56: "Deletion of the edge (y_j, t) […] Insertion of a new edge
  (x_i, t) of color p + j"): at most `2` coloured updates confined to `E_Q`: insertions of pairs of
  `E_Q ∖ E₁` with any cost and colour, deletions of pairs of `E₁`, colour changes of surviving pairs
  of `E₁`. The answer is whether the coloured multigraph `G + U` has a colorful spanning tree.
* Oracle model, error `δ ∈ [0, 1/2)` and space as in `theorem_10_1`. -/
theorem theorem_10_2 :
    ∀ δ : ℝ, 0 ≤ δ → δ < 1 / 2 → ∃ c c₁ C : ℝ, 0 < c ∧ 0 < c₁ ∧
      ∀ n ms : ℕ, 4 ≤ ms → ms ≤ n * (n - 1) →
        ∃ (χ : Fin n × Fin n → Fin (n - 1)) (EQ E₁ T : Finset (Fin n × Fin n)) (𝒢 : Set (InputGraph n)),
          (∀ e ∈ EQ, e.1 < e.2) ∧ c₁ * ms ≤ (EQ.card : ℝ) ∧ (EQ.card : ℝ) ≤ C * ms ∧
          T.card + 1 = n ∧
          (∀ G ∈ 𝒢, G.Undirected ∧ G.E ∩ EQ = E₁ ∧ T ⊆ G.E ∧
            ∃ X, IsColorful (cGraph (cEdges G χ ⟨[], ∅, []⟩)) (cColor (cEdges G χ ⟨[], ∅, []⟩)) X ∧
              ∀ i ∈ X, ((cGraph (cEdges G χ ⟨[], ∅, []⟩)).arcs.tail i,
                (cGraph (cEdges G χ ⟨[], ∅, []⟩)).arcs.head i) ∈ T) ∧
          let Qs : Set (CUpdate n) := {U | U.size ≤ 2 ∧
            (∀ x ∈ U.ins, (x.1, x.2.1) ∈ EQ \ E₁) ∧ U.del ⊆ E₁ ∧ ∀ r ∈ U.recol, r.1 ∈ E₁ \ U.del}
          ∀ O : InfoOracle (InputGraph n) (CUpdate n) Bool,
            O.Correct 𝒢 Qs (fun G U => decide (HasColorfulTree (cEdges G χ U))) δ →
              O.SpaceAtLeast 𝒢 (c * min ((ms : ℝ) ^ 2) ((n : ℝ) ^ 2)) := by sorry

end MatroidSensOracle.Supplement
