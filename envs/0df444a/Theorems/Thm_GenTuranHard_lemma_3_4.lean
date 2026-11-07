-- Prove2me | Theorems.Thm_GenTuranHard_lemma_3_4
-- name    : GenTuranHard.lemma_3_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:36:57.092313+00:00
-- url     : https://prove2.me/theorems/bdbe23a2-c445-4446-8cb7-8762503a61e0
-- title:
--   Lemma 3.4 [ASS09] — on dense graphs $\mathrm{cut}_{k-1}(G) = \mathrm{ex}(G,K_2,K_k)$, and computing it is NP-hard
-- statement:
--   For every integer $k \ge 3$ there exist constants $\mu = \mu(k) > 0$ and $n_0 = n_0(k)$ such that every $n$-vertex graph $G$ with $n \ge n_0$ and $\delta(G) \ge (1 - \mu) n$ satisfies
--
--   $$
--   \mathrm{cut}_{k-1}(G) = \mathrm{ex}(G, K_2, K_k).
--   $$
--
--   Moreover, computing $\mathrm{cut}_{k-1}(G)$ exactly is NP-hard when restricted to these graphs.
--
--   The paper derives this from Alon, Shapira and Sudakov [ASS09, Theorem 6.1(i) and §8] and supplies a proof sketch. It is the source problem of the reduction: on the class $\mathcal G_k$ the value $z = \mathrm{cut}_{k-1}(G)$ is hard to compute and equals the largest number of edges of a $K_k$-free subgraph.
--
--   **Formalization Note** One pair $\mu, n_0$ serves both clauses. $\mathrm{ex}(G, K_2, K_k)$ counts copies of $K_2$, i.e. edges, of a $K_k$-free subgraph. Exact computation is NP-hardness with error $0$ on the class $\mathcal G_k$.
--
--   Differences from the source:
--   - reading: “NP-hard” (unspecified reduction notion) → AddApproxNPHard: for every NP language a polynomial-time instance map and a polynomial-time answer map that uses one approximate value, correct for every admissible rational answer; reason: the reductions of Theorem 3.2 and Corollary 3.3 have this one-query form; it implies hardness under polynomial-time oracle (Cook) reductions
--   - encoding: input graphs and rational numbers (format unspecified) → encGraph (n in unary, then the n² adjacency bits) and encRat (sign, |numerator|, denominator in a self-delimiting binary code); reason: explicit injective codes; polynomial time in the code length of encGraph is polynomial time in n
--   - encoding: ex(G, K₂, K_k), the maximum number of copies of K₂ in a K_k-free subgraph of G → exT G (⊤ on Fin 2) {K_k}: Finset.sup over G.Subgraph of copyCount; reason: a finite maximum in ℕ; copies of K₂ in H are the edges of H
-- source:
--   Chen, He, Li, Ma, Xie, NP-hardness of additive approximation for generalized Turán problems, arXiv:2610.16358 (sha256 dc85633a…), Lemma 3.4, p.12 (from [ASS09, Theorem 6.1(i), Section 8])

import Mathlib
import Definitions.Def_GenTuranHard_exT
import Definitions.Def_GenTuranHard_cutR
import Definitions.Def_GenTuranHard_AddApproxNPHard

set_option autoImplicit false

namespace GenTuranHard

/-- **Lemma 3.4** ([ASS09]; Chen, He, Li, Ma, Xie, arXiv:2610.16358, sha256 dc85633a…, Lemma 3.4, p.12).
For every integer `k ≥ 3` there are constants `µ = µ(k) > 0` and `n₀ = n₀(k)` such that every `n`-vertex
graph `G` with `n ≥ n₀` and `δ(G) ≥ (1 − µ)n` satisfies `cut_{k−1}(G) = ex(G, K₂, K_k)`; moreover,
computing `cut_{k−1}(G)` exactly is NP-hard restricted to these graphs.

**Formalization Note** The paper cites [ASS09, Theorem 6.1(i), §8, Claim 8.3] and gives a proof sketch;
here it is posed, not assumed. One pair `µ, n₀` serves both clauses. `ex(G, K₂, K_k)` is the largest
number of copies of `K₂`, i.e. of edges, in a `K_k`-free subgraph of `G`. "Computing exactly is
NP-hard" is `AddApproxNPHard` with error `0` on the domain `𝒢_k = InGk µ n₀`. -/
theorem lemma_3_4 (k : ℕ) (hk : 3 ≤ k) :
    ∃ μ : ℝ, 0 < μ ∧ ∃ n0 : ℕ,
      (∀ G : FinGraph, InGk μ n0 G →
        cutR (k - 1) G.2 = exT G.2 (⊤ : SimpleGraph (Fin 2)) {cliqueFG k}) ∧
      AddApproxNPHard encGraph (InGk μ n0) (fun G => (cutR (k - 1) G.2 : ℝ)) (fun _ => 0) := by sorry

end GenTuranHard
