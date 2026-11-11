-- Prove2me | Theorems.Thm_OncePaid_Sparse_lemma_3_1
-- name    : OncePaid.Sparse.lemma_3_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T13:46:38.769201+00:00
-- url     : https://prove2.me/theorems/6a89937d-d821-417d-9021-e903ccad429c
-- title:
--   Lemma 3.1 — every gate is the minimum of its parse forms; output forms majorize; disjoint substitution gives a valid parse
-- statement:
--   Let $C$ be a min-plus circuit with positive scalar gates and finite real constants (of any sign) over the prices $c\in\mathbb R^\iota$, with $\iota$ finite. For a gate $u$ write $C_u(c)$ for its value and $\mathcal P_u$ for the set of formal parses of $u$, each computing an affine form $P(c)=\beta(P)+\sum_x\alpha_x(P)c_x$. Then:
--
--   1. for every gate $u$, $\mathcal P_u$ is finite, every form of a parse in $\mathcal P_u$ has nonnegative price coefficients, and $u$ computes their minimum:
--
--   $$
--   C_u(c)=\min_{P\in\mathcal P_u}P(c)\qquad\text{for all }c\in\mathbb R^\iota;
--   $$
--
--   2. in particular every output form majorizes the circuit pointwise, $P(c)\ge C(c)$, and at every input $c$ some output form attains $C(c)$;
--   3. replacing pairwise disjoint occurrences in an output parse by local parses of the same original gates gives another valid output parse.
--
--   The lemma is the bridge from circuits to affine forms: the lower bounds evaluate attaining parses at test prices and exchange subparses between them.
--
--   Differences from the source:
--   - reading: "every gate computes the minimum of a finite family of affine forms" → the family is the set of forms of the gate's formal parses (finite, all majorize, one attains at each input); reason: this is the family the proof and §2.2 use, and it implies the existential statement.
--   - encoding: a finite DAG with shared gates → a well-formed straight-line program (`Circuit.WF`); formal parses → trees `PTree` with the validity predicate `IsParse`; occurrences → positions (lists of child choices); reason: Lean representation, same circuits and parses.
--   - encoding: replacing several disjoint occurrences → a list of (position, parse) pairs with pairwise non-prefix positions, each parse rooted at the gate of the occurrence it replaces, applied in order; reason: Lean representation of a simultaneous substitution (disjointness makes the order irrelevant).
-- source:
--   Chao, Li, Gao, Wang, Once-Paid Subsequences and the Cost of Min-Plus Approximation, STOC 2027 submission (manuscript sha256 9dc21472…), p. 12, Lemma 3.1 (PDF p. 14)

import Mathlib
import Definitions.Def_OncePaid_Sparse_Circuit
import Definitions.Def_OncePaid_Sparse_Parse

namespace OncePaid.Sparse

/-- Lemma 3.1 (Parses and substitution), p. 12. For a well-formed min-plus circuit with positive
scalar gates and finite signed constants:
(1) every gate `u` computes the minimum of the finite family of affine forms of its formal parses,
and each of these forms has nonnegative price coefficients;
(2) every output form majorizes the circuit pointwise, and some output form attains its value at
every input;
(3) replacing pairwise disjoint occurrences in an output parse by local parses of the same
original gates gives another valid output parse. -/
theorem lemma_3_1 {ι : Type} [Fintype ι] (C : Circuit ι) (hC : C.WF) :
    (∀ u < C.gates.length,
      {t : PTree | C.IsParse t ∧ t.root = u}.Finite ∧
      (∀ t : PTree, C.IsParse t → t.root = u → (C.parseForm t).NonnegCoef) ∧
      ∀ c : ι → ℝ,
        (∀ t : PTree, C.IsParse t → t.root = u → C.gateValue c u ≤ (C.parseForm t).eval c) ∧
        ∃ t : PTree, C.IsParse t ∧ t.root = u ∧ (C.parseForm t).eval c = C.gateValue c u) ∧
    (∀ c : ι → ℝ,
      (∀ t : PTree, C.IsParse t → t.root = C.output → C.eval c ≤ (C.parseForm t).eval c) ∧
      ∃ t : PTree, C.IsParse t ∧ t.root = C.output ∧ (C.parseForm t).eval c = C.eval c) ∧
    (∀ (P : PTree) (subs : List (List ℕ × PTree)),
      C.IsParse P → P.root = C.output → PTree.DisjointPositions subs →
      (∀ s ∈ subs, ∃ t' : PTree, P.subtreeAt s.1 = some t' ∧ C.IsParse s.2 ∧
        s.2.root = t'.root) →
      C.IsParse (P.replaceAll subs) ∧ (P.replaceAll subs).root = C.output) := by sorry

end OncePaid.Sparse
