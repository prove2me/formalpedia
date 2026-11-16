-- Prove2me | Theorems.Thm_MatroidSensOracle_Supplement_theorem_4_3
-- name    : MatroidSensOracle.Supplement.theorem_4_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T03:09:35.452698+00:00
-- url     : https://prove2.me/theorems/6c241554-92cb-438e-955a-a19b60728cdd
-- title:
--   Theorem 4.3 (component-count and all-pairs connectivity oracle), $O(f\min(m,fn))$ space, $O(f^\omega\log f)$ query
-- statement:
--   There are absolute constants $C_{\mathrm{err}}$ and $d$ such that, for every finite field $\mathbb F$ with $\omega=\omega_{\mathbb F}$ and every $\tau>0$, there are a constant $C$ and one data structure on the algebraic RAM over $\mathbb F$ with the following properties. It preprocesses a connected undirected graph $G$ on $n$ vertices and $m$ edges and stores at most $C\,f\min(m,fn)$ cells. For every update $U=(F,I)$ with $|F|+|I|\le f$ it supports, each in at most $C\,f^{\omega+\tau}\log_2(f+1)$ steps:
--
--   1. **Component count:** report the number $c(G+U)$ of connected components of $G+U$;
--   2. **All-pairs connectivity:** given $x,y\in V$, decide whether $x$ and $y$ are connected in $G+U$.
--
--   Each fixed query is answered correctly with probability at least
--   $$1-\frac{C_{\mathrm{err}}\,n^{d}}{|\mathbb F|}.$$
--
--   This oracle is the first graph application of the single-matroid basis oracle (Theorem 3.2), applied to the graphic matroid.
--
--   **Formalization Note** $G$ is an undirected simple graph (edges $(a,b)$ with $a<b$); an update deletes edges of $G$ and inserts edges between distinct vertices, possibly parallel ones. No preprocessing time is printed; the preprocessing is only required to halt within a bound depending on $n$, $m$ and $f$.
--
--   Differences from the source:
--   - reading: sensitivity oracles for a matroid represented over F (machine unstated) → oracles on the base algebraic RAM over the finite field F (AOracle): time counts all word and field instructions, worst case over the coins; space counts stored word and field cells; the error is over the coins, per fixed query; reason: the machine of the published base milestones Theorems 3.5 and 3.7
--   - encoding: O(x^ω) → C·x^{ω+τ} for every τ > 0, with ω = omega F; reason: ω is an infimum that need not be attained; base convention
--   - reading: success probability 1 − poly(n)/|F| → 1 − C_err·n^d/|F| with absolute C_err and d chosen before the field; reason: the proof gives N/|F| per determinant test and O(log f) tests
--   - encoding: log f → log₂(f + 1); reason: so that f = 1 does not zero the bound
--   - reading: no preprocessing time is printed → the preprocessing halts within some bound TP depending only on the size parameters; reason: the theorem bounds only space and query time; finitely many instances share given parameters, so halting is all that is asserted
--   - reading: an undirected graph → an input graph whose every edge is written (a, b) with a < b (no loops, no parallel input edges); inserted edges join two distinct vertices; reason: the paper's convention on p.39: 'an edge e in G is written as (a, b), where a < b'
--   - reading: a data structure supporting each of the two queries → one oracle; the query words start with 0, 0, 0 (component count) or 1, x, y (connectivity), followed by the update; reason: one data structure serves both kinds of query
--   - encoding: an n-vertex graph and the parameters of the bounds → f ≥ 1; n ≥ 1 follows from connectivity; reason: nondegeneracy: the printed O(·) bounds are positive and the objects are defined
-- source:
--   Choudhary, Kumar, Saggi, Sensitivity Oracles for Matroid Packing, Matroid Covering, and Matching Problems with Applications, arXiv:2609.01283 (held version, sha256 0de50841…), Theorem 4.3, p.24 (PDF p.27)

import Mathlib
import Definitions.Def_MatroidSensOracle_AlgRAM
import Definitions.Def_MatroidSensOracle_Supplement_GraphProblems
import Definitions.Def_OAI_MatrixMultiplication_Arithmetic_omega

set_option autoImplicit false

namespace MatroidSensOracle.Supplement

/-- **Theorem 4.3 (Component-count and all-pairs connectivity oracle).** Choudhary, Kumar, Saggi,
arXiv:2609.01283 (held version, sha256 0de50841…), p.24 (PDF p.27): "There is a randomized algorithm
that preprocesses a connected graph G on n vertices and m edges into an O(f min(m, fn)) space data
structure that, for any update U = (F, I) with |F| + |I| ⩽ f, supports each of the following queries
in O(f^ω log f) time:
• Component Count: Report the number c(G + U) of connected components in the updated graph G + U;
• All-Pairs Connectivity: Given any two vertices x, y ∈ V, decide whether x and y are connected in
  G + U.
All queries succeed with probability at least 1 − poly(n)/|F|."

**Formalization Note.**
* Machine: the base algebraic RAM over the finite field `F` (`AOracle`), space in stored cells, time
  worst case over the coins, error per fixed query. `ω = omega F`; `O(f^ω log f)` is
  `C f^{ω+τ} log₂(f + 1)` for every `τ > 0`.
* `poly(n)/|F|` is `Cerr n^d / |F|` with `Cerr`, `d` absolute, chosen before the field. No
  preprocessing time is printed: the preprocessing only has to halt within some bound `TP(n, m, f)`.
* `G` is an undirected simple graph (edges `(a, b)`, `a < b`), connected, with input words
  `encodeWith G [n, f]`. One data structure answers both kinds of query: the query words are
  `0, 0, 0` (component count) or `1, x, y` (connectivity of `x`, `y`), followed by `U.encode`. An
  update deletes `F ⊆ E` and inserts edges between distinct vertices (parallel edges allowed).
* Output: word `0` is `c(G + U)` (component count), resp. `1` exactly when `x`, `y` are connected in
  `G + U`. -/
theorem theorem_4_3 :
    ∃ (Cerr : ℝ) (d : ℕ), ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F],
    ∀ τ : ℝ, 0 < τ → ∃ (C : ℝ) (b : ℕ) (O : AOracle) (TP : ℕ → ℕ → ℕ → ℝ),
      ∀ (n f : ℕ) (G : InputGraph n), G.Undirected → (adj G.toMultigraph).Connected → 1 ≤ f →
      ∀ w : ℕ, b * (Nat.log 2 (n + f + 2) + 1) ≤ w →
        let ω := OAI.MatrixMultiplication.Arithmetic.omega F
        let q : ℝ := Fintype.card F
        let m : ℕ := (pairList n G.E).length
        let inp : List ℤ := encodeWith G [(n : ℤ), f]
        let TPn : ℕ := ⌊TP n m f⌋₊
        let TQ : ℕ := ⌊C * (f : ℝ) ^ (ω + τ) * Real.logb 2 ((f : ℝ) + 1)⌋₊
        let err : ℝ := Cerr * (n : ℝ) ^ d / q
        O.PrepWithin w inp ([] : List F) TPn (C * ((f : ℝ) * ((min m (f * n) : ℕ) : ℝ))) ∧
        ∀ U : Update n, G.ValidUPlain f U →
          (O.QueryWithin w inp ([] : List F) ([0, 0, 0] ++ U.encode) [] TPn TQ ∧
            O.ErrorAtMost w inp ([] : List F) ([0, 0, 0] ++ U.encode) [] TPn TQ
              (fun wm => (wm 0).toNat = compCount (G.plus U)) err) ∧
          ∀ x y : Fin n,
            O.QueryWithin w inp ([] : List F) ([1, ((x : ℕ) : ℤ), ((y : ℕ) : ℤ)] ++ U.encode) [] TPn TQ ∧
            O.ErrorAtMost w inp ([] : List F) ([1, ((x : ℕ) : ℤ), ((y : ℕ) : ℤ)] ++ U.encode) [] TPn TQ
              (fun wm => ((wm 0).toNat = 1 ↔ Connected (G.plus U) x y)) err := by sorry

end MatroidSensOracle.Supplement
