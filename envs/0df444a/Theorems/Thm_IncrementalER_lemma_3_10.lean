-- Prove2me | Theorems.Thm_IncrementalER_lemma_3_10
-- name    : IncrementalER.lemma_3_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T17:07:48.039193+00:00
-- url     : https://prove2.me/theorems/a9669e2a-d40e-4707-93ad-e31fe9f5f624
-- title:
--   Lemma 3.10, p.13 — $\ell^G_U(v)\le\alpha+\beta$ above an $\alpha$-hitting set with $\Gamma_T\le\beta$
-- statement:
--   Let $G$ be a connected graph and let $T$ be an $\alpha$-hitting set of $G$ (Definition 3.9) whose congestion bound is $\Gamma_T(v)\le\beta$ for every $v\notin T$. Then for every $U\supseteq T$ and every $v\in U\setminus T$,
--
--   $$\ell^G_U(v)\le\alpha+\beta .$$
--
--   With $\beta=\tilde O(\alpha^2)$, as in Definition 3.9, this is the printed bound $\ell^G_U(v)\le\tilde O(\alpha^2)$; it bounds the width of the paper's multiplicative-weights instances. Connectivity is the paper's standing assumption ("We assume throughout that everywhere we are dealing exclusively with connected graphs", p.10) and is a hypothesis.
--
--   Differences from the source:
--   - encoding: G = (V, E, c) an undirected capacitated multigraph (p.10) → a symmetric nonnegative conductance function with zero diagonal (parallel capacities added, no loops); reason: the Laplacian, effective resistances, leverage degrees and the random walk are unchanged by merging parallel edges; the paper's edges (u, v) join two vertices, and the source never uses loops
--   - generalization: item 2 of Definition 3.9, Γ_T(v) ≤ Õ(α²), and the conclusion ℓ^G_U(v) ≤ Õ(α²) → Γ_T(v) ≤ β for a parameter β, and ℓ^G_U(v) ≤ α + β; reason: Õ(α²) has no meaning without a constant; with β = Õ(α²) the conclusion α + β is Õ(α²), and α + β is what the proof on p.13 gives
--   - generalization: deg(v) the multigraph degree in items 2 and 3 of Definition 3.9 → deg(v) the number of distinct neighbours; reason: it is at most the multigraph degree, so every α-hitting set of the multigraph is one in Lean, and ℓ^G_U is unchanged
-- source:
--   Goranci, Kyng, Probst Gutenberg, Zhao, Zöcklein, Incremental All-Pairs Effective Resistance in Almost-Linear Time, STOC 2027 submission (manuscript sha256 a0415fd5…), Lemma 3.10 and its proof, p.13; Definition 3.9 and (3), p.13; connectivity, p.10

import Mathlib
import Definitions.Def_IncrementalER_scCond
import Definitions.Def_IncrementalER_hitBefore

namespace IncrementalER

/-- **Lemma 3.10** (leverage degrees above a hitting set), with Definition 3.9.

Goranci, Kyng, Probst Gutenberg, Zhao, Zöcklein, *Incremental All-Pairs Effective Resistance in
Almost-Linear Time*, STOC 2027 submission (manuscript sha256 a0415fd5…), Lemma 3.10 and its proof, p.13; Definition 3.9 and (3), p.13; connectivity assumption, p.10.

Let `G` be a connected graph and `T` an `α`-hitting set whose congestion bound (item 2 of
Definition 3.9) is `Γ_T(v) ≤ β`. Then for every `U ⊇ T` and every `v ∈ U \ T`,
`ℓ^G_U(v) ≤ α + β`.

**Formalization Note.** Definition 3.9 bounds `Γ_T(v)` by `Õ(α²)`, which has no meaning without a
constant; the bound is the parameter `β` and the conclusion `α + β` is what the proof on p.13
gives. With `β = Õ(α²)` it is the printed `Õ(α²)`. Degrees are counted in the collapsed graph,
which makes item 3 of the definition no stronger than for the multigraph. -/
theorem lemma_3_10 {V : Type*} [Fintype V] [DecidableEq V] (c : V → V → ℝ) (hc : IsGraph c)
    (hconn : Connected c) (T : Finset V) (α β : ℝ) (hT : IsHittingSet c T α β)
    (U : Finset V) (hTU : T ⊆ U) (v : V) (hvU : v ∈ U) (hvT : v ∉ T) :
    levDegT c U v ≤ α + β := by sorry

end IncrementalER
