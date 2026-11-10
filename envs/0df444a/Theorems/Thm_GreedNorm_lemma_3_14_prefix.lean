-- Prove2me | Theorems.Thm_GreedNorm_lemma_3_14_prefix
-- name    : GreedNorm.lemma_3_14_prefix
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T21:44:50.21876+00:00
-- url     : https://prove2.me/theorems/bedacadd-390b-4aba-96ab-ccebb5a2922c
-- title:
--   Proof of Lemma 3.14 — the $k$ lowest-valued elements minimize $f(v[S])$ among $k$-sets
-- statement:
--   Let $v\in\mathbb R^n_{\ge0}$ be values on a universe $U$ of $n$ elements and $f$ a monotone symmetric norm on $\mathbb R^n$.
--
--   1. For every $k\le n$ there is a set $S_k$ of $k$ elements with the lowest values: $v(a)\le v(b)$ for all $a\in S_k$, $b\notin S_k$.
--   2. Every such set satisfies $f(v[S_k])\le f(v[S'])$ for every $S'$ with $|S'|=k$.
--   3. Consequently, if some $S'$ satisfies $f(v[S'])\le B$, then every lowest-values set $S$ with $|S|=|S'|$ also satisfies $f(v[S])\le B$.
--
--   Hence the largest $k$ with $f(v[S_k])\le B$ gives an optimal solution of Norm-Budgeted Cardinality Maximization: maximize $|S|$ subject to $f(v[S])\le B$.
--
--   Differences from the source:
--   - encoding: monotone symmetric norms on the orthant R^k_{≥0} → R_{≥0} → functions (Fin k → ℝ) → ℝ satisfying the public SymNormLoad.IsMonotoneSymmetricNorm (a norm on all of ℝ^k, monotone on the orthant); reason: every monotone symmetric norm on the orthant extends to ℝ^k by x ↦ g(|x|), and only orthant values are ever used; same instances
--   - encoding: for k ≥ 0, the subset S_k of k elements with the lowest values → for k ≤ n there is such a set; clauses 2–3 are stated for every lowest-values set; reason: a k-element subset of an n-element universe exists only for k ≤ n; ties make S_k non-unique, so every choice is covered
--   - reading: therefore the optimal solution is S_{k*}, k* the largest k with f(v[S_k]) ≤ B → clause 3: whenever some S' is feasible, every lowest-values set of size |S'| is feasible; reason: this is the optimality of the largest feasible prefix, stated without fixing a choice of S_k
--   - generalization: a budget B ≥ 0 (Definition 3.13) → clause 3 for every real B; reason: no step uses B ≥ 0, and the source's budgets are among the real ones, so the statement specializes to the source's
-- source:
--   Gan–Huang–Umboh, Greed is All You Need: An Approximation Algorithm Framework for Nested Norm Covering and Packing Problems, manuscript (STOC 2027 submission, held version sha256 2a3d250c…a300b1b6), proof of Lemma 3.14, p.9 (PDF 11)

import Mathlib
import Definitions.Def_SymNormLoad_IsMonotoneSymmetricNorm
import Definitions.Def_GreedNorm_vecOn

namespace GreedNorm

/-- **Prefix optimality for NormBudgCard** (the proof of Lemma 3.14).
Gan–Huang–Umboh, *Greed is All You Need: An Approximation Algorithm Framework for Nested Norm
Covering and Packing Problems*, manuscript (STOC 2027 submission, held version sha256 2a3d250c…a300b1b6), proof of Lemma 3.14, p.9 (PDF 11): "For k ≥ 0, define the subset Sk of k elements with the
lowest values. Now observe that for any other subset S′ with |S′| = k, we have that
v[Sk]↓ ≤ v[S′]↓. By monotonicity and symmetry of f, we have f(v[Sk]) = f(v[Sk]↓) ≤ f(v[S′]↓) =
f(v[S′]). Therefore, the optimal solution is Sk∗ where k∗ is the largest k such that
f(v[Sk]) ≤ B."

For `v ≥ 0` and a monotone symmetric norm `f` on `ℝ^n`:
1. for every `k ≤ n` there is a set `S_k` of `k` elements of lowest values
   (`v a ≤ v b` for `a ∈ S_k`, `b ∉ S_k`);
2. every such `S` has `f(v[S]) ≤ f(v[S'])` for every `S'` with `|S'| = |S|`;
3. hence, if some `S'` has `f(v[S']) ≤ B`, every lowest-values set of size `|S'|` also has
   `f(v[S]) ≤ B` (so a largest feasible prefix is optimal).

**Formalization Note** Universe `U = Fin n`; `v[S]` is `vecOn v S`. -/
theorem lemma_3_14_prefix {n : ℕ} (v : Fin n → ℝ) (hv : ∀ j, 0 ≤ v j)
    (f : (Fin n → ℝ) → ℝ) (hf : SymNormLoad.IsMonotoneSymmetricNorm f) :
    (∀ k ≤ n, ∃ S : Finset (Fin n), S.card = k ∧ ∀ a ∈ S, ∀ b ∉ S, v a ≤ v b) ∧
      (∀ S : Finset (Fin n), (∀ a ∈ S, ∀ b ∉ S, v a ≤ v b) →
        ∀ S' : Finset (Fin n), S'.card = S.card → f (vecOn v S) ≤ f (vecOn v S')) ∧
      (∀ (B : ℝ) (S' : Finset (Fin n)), f (vecOn v S') ≤ B →
        ∀ S : Finset (Fin n), S.card = S'.card → (∀ a ∈ S, ∀ b ∉ S, v a ≤ v b) →
          f (vecOn v S) ≤ B) := by sorry

end GreedNorm
