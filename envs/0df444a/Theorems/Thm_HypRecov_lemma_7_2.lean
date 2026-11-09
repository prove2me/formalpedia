-- Prove2me | Theorems.Thm_HypRecov_lemma_7_2
-- name    : HypRecov.lemma_7_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T16:37:49.821339+00:00
-- url     : https://prove2.me/theorems/defa27bf-7e53-4aca-8ebc-ffc35835403a
-- title:
--   Lemma 7.2 — exact filtering
-- statement:
--   Let $H$ be a finite simple hypergraph on $V$ and $k\ge0$. For every edge $e$ of $H$ with $|e|\ge 2$,
--   $$e\in\mathcal B_k(H)\iff\min_{u,v\in e,\ u\ne v}\lambda_H(u,v)<k,$$
--   where $\lambda_H(u,v)$ is the minimum value of a cut separating $u$ and $v$. The same equivalence holds with $\lambda_{\widehat H}$ for every weighted hypergraph $\widehat H$ with $\min\{\mathrm{cut}_H(S),k\}=\min\{\mathrm{cut}_{\widehat H}(S),k\}$ for all $S$.
--
--   With the representation of Lemma 7.1 the final output can be filtered to exactly $\mathcal B_k(H)$ by minimum-cut computations.
--
--   Differences from the source:
--   - encoding: min over pairs u ≠ v of λ(u, v) is below k → some pair u ≠ v of e has λ(u, v) < k; reason: equivalent for a finite nonempty set of pairs
--   - generalization: H simple r-uniform → any finite family of vertex sets; Ĥ with natural weights; reason: the proof does not use uniformity
-- source:
--   Zhang, Chen, Shen, Hypergraph Recovery from Anonymous Projection Streams, STOC 2027 submission (manuscript sha256 719dcfff4dc2eba2d8c5a3c51679a08cfb11f076546dea963c6376a2b9da2c82), Lemma 7.2, p.19 (PDF p.20)

import Mathlib
import Definitions.Def_HypRecov_crisp
import Definitions.Def_HypRecov_cutW
import Definitions.Def_HypRecov_lam

namespace HypRecov

/-- **Lemma 7.2 (Exact filtering).** Zhang, Chen, Shen, *Hypergraph Recovery from Anonymous Projection
Streams*, STOC 2027 submission (manuscript sha256 719dcfff…), Lemma 7.2, p.19 (PDF p.20): "For every
original edge e of size at least two, e ∈ ℬ_k(H) ⟺ min_{u,v∈e, u≠v} λ_H(u, v) < k, where λ_H(u, v) is
the minimum capacity of a cut separating u and v. The same test using Ĥ is equivalent whenever Ĥ
preserves all cuts truncated at k."

**Formalization Note.** "The minimum over pairs is below `k`" is written "some pair `u ≠ v` of `e` has
`λ(u, v) < k`". The hypergraph is any finite simple hypergraph on `Fin n`, and `Ĥ` any weighted
hypergraph with `min{cut_H(S), k} = min{cut_Ĥ(S), k}` for all `S`. -/
theorem lemma_7_2 {n : ℕ} (E : Finset (Finset (Fin n))) (k : ℕ) :
    (∀ e ∈ E, 2 ≤ e.card →
      (e ∈ crisp E k ↔ ∃ u ∈ e, ∃ v ∈ e, u ≠ v ∧ lam E u v < k)) ∧
    ∀ H : List (Finset (Fin n) × ℕ), (∀ S : Finset (Fin n), min (cut E S) k = min (cutW H S) k) →
      ∀ e ∈ E, 2 ≤ e.card →
        (e ∈ crisp E k ↔ ∃ u ∈ e, ∃ v ∈ e, u ≠ v ∧ lamW H u v < k) := by sorry

end HypRecov
