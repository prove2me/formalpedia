-- Prove2me | Theorems.Thm_HardCoreLocalSampling_Local_deletion_contexts_and_pinnings
-- name    : HardCoreLocalSampling.Local.deletion_contexts_and_pinnings
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:55:21.054587+00:00
-- url     : https://prove2.me/theorems/9f119bb2-2105-48be-a807-01889d32d180
-- title:
--   Lemma 14 — Deletion contexts and pinnings
-- statement:
--   Fix $\Delta\ge3$. A subproblem at factory generation $\ell$ is represented by the original oracles and a list of at most $\Delta(\ell+1)$ deleted labels. Then:
--
--   1. There are a program, a polynomial $p$ independent of $n$, and a constant $C$ such that on every graph of maximum degree at most $\Delta$ with a feasible pinning, for every such list and every query vertex $x$ of the remaining graph, the program returns the $i$th neighbor of $x$ in the residual graph (the graph left after the list's deletions and the pin deletions) in label order, or reports none. It uses at most $p(\ell+1)$ intrinsic work and at most $C$ underlying graph and pinning queries.
--   2. For each fixed height $h$ there are such $P,p,C$ for computing the depth-$h$ view of the residual subproblem.
--
--   Thus subproblems are accessed lazily without copying the graph, center and coefficient calculations have graph-context overhead polynomial in $\ell+1$, and pinning adds only a parameter-dependent constant factor to each local query.
--
--   Differences from the source:
--   - encoding: an algorithm in the informally described word and bit cost model → a finite program of the Machine language; reason: a concrete instruction set of that model; every such program is an algorithm in the source's model, and restricting address arithmetic to increment, decrement and paid conversion only charges more than the source does
--   - encoding: graph-context overhead of every center and coefficient calculation → a routine computing the depth-h view, on which centers and coefficients depend only through arithmetic; reason: coefficients depend on the graph only through the centers, which depend on it only through the view; this is the graph-dependent part of the calculation
--   - encoding: feasible pinning adds a constant factor to each underlying local query → each residual neighbor query uses at most a constant number of oracle queries, counted by the machine; reason: this is the same bound, with the query count read from the run
-- source:
--   Thomas Chen, STOC 2027 submission #462 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/462.pdf, Lemma 14, printed p.11 (PDF p.12)

import Mathlib
import Definitions.Def_HardCoreLocalSampling_Local_Specs

namespace HardCoreLocalSampling.Local

/-- Thomas Chen, STOC 2027 submission #462, Lemma 14, printed p.11 (PDF p.12).
Fixing `Δ`, a context at generation `ℓ` is a deletion list of at most `Δ(ℓ+1)` labels on the
original oracle (nothing is copied). (1) One neighbor query in the residual graph, label-sorted,
over a feasible pinning, costs at most `p(ℓ+1)` intrinsic work with `p` independent of `n`, and
at most a constant number `C` of underlying graph and pin queries. (2) For each fixed height, the
unfolding on which center and coefficient calculations depend is computed with the same
bounds. -/
theorem deletion_contexts_and_pinnings (Delta : ℕ) (hDelta : 3 ≤ Delta) :
    (∃ (P : Program) (p : Polynomial ℕ) (C : ℕ),
      ∀ (I : LocalInstance), ValidInput I Delta →
      ∀ (l : ℕ) (D : List I.vertices), D.length ≤ Delta * (l + 1) →
      ∀ (x : I.vertices), x ∉ contextDeleted D → ∀ (i : ℕ) (ω : ℕ → Bool),
        RunsTo P I.oracle ω noExt (contextConfig D x i) (p.eval (l + 1)) C fun c =>
          match (orderedNeighbors I.graph (contextDeleted D) x)[i]? with
          | some u => c.result = some true ∧ c.L 0 = u.val
          | none => c.result = some false) ∧
    (∀ h : ℕ, ∃ (P : Program) (p : Polynomial ℕ) (C : ℕ),
      ∀ (I : LocalInstance), ValidInput I Delta →
      ∀ (l : ℕ) (D : List I.vertices), D.length ≤ Delta * (l + 1) →
      ∀ (x : I.vertices), x ∉ contextDeleted D → ∀ ω : ℕ → Bool,
        RunsTo P I.oracle ω noExt (contextConfig D x 0) (p.eval (l + 1)) C fun c =>
          c.A 0 = (deletionView I.graph h (contextDeleted D) x).length ∧
          ∀ j, c.Nm j = (deletionView I.graph h (contextDeleted D) x).getD j 0 ∨
            (deletionView I.graph h (contextDeleted D) x).length ≤ j) := by sorry

end HardCoreLocalSampling.Local
