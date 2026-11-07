-- Prove2me | Theorems.Thm_MinSumClust_lemma_52
-- name    : MinSumClust.lemma_52
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:47:38.079335+00:00
-- url     : https://prove2.me/theorems/07aebb0e-9cec-4189-85ae-c30cdb20437e
-- title:
--   Lemma 52 — expected extra cost of random sets assigned to one cluster, display (29)
-- statement:
--   Let $d$ be a pseudometric on a finite set $D$, $S\subseteq D$, and $T_1,\dots,T_m\subseteq D$ disjoint nonempty sets; let $R_i=S\cap T_i$ and $p_i=|R_i|/|T_i|$. Let $(Z_1,\dots,Z_m)$ be random sets with $Z_i\subseteq T_i$, and let $a,b\ge 0$ be such that
--
--   1. $\Pr[u\in Z_i]\le a\,p_i$ for every $i$ and $u\in T_i$;
--   2. $\Pr[u\in Z_i,\ v\in Z_j]\le b\,p_ip_j$ for every $i\ne j$, $u\in T_i$, $v\in T_j$.
--
--   Then
--
--   $$\mathbb E\Bigl[2\sum_i d(S,Z_i)+\sum_{i,j}d(Z_i,Z_j)\Bigr]\ \le\ (2a+b)\,\mathrm{cost}(S)+(2a+2b)\sum_i\frac{|S|}{|T_i|}\,d(R_i,T_i)+a\sum_ip_i\,\mathrm{cost}(T_i),\qquad(29)$$
--
--   where $\sum_{i,j}$ includes $i=j$. This bounds the expected extra cost of the cluster $S\cup\bigcup_iZ_i$.
--
--   Differences from the source:
--
--   - generalization: d is a metric → d is any pseudometric (distinct points may be at distance 0); reason: the argument uses only nonnegativity, symmetry, the zero diagonal and the triangle inequality; every metric is a pseudometric, so the paper's statement is the special case
--   - encoding: random sets Z_i ⊆ T_i → any joint distribution (PMF) of (Z₁, …, Z_m) whose support has Z_i ⊆ T_i; reason: every distribution of finitely many finite sets is such a PMF
-- source:
--   Anand, Charikar, Gao, Grandoni, Lee, Sharma, van Wijland, A Constant Approximation for Min-sum k-Clustering, STOC 2027 submission (manuscript of November 3, 2026, sha256 103c52a5…), Lemma 52, p.51 (PDF p.53), display (29)

import Mathlib
import Definitions.Def_MinSumClust_cost
import Definitions.Def_MinSumClust_IsMetric
import Definitions.Def_MinSumClust_pexp

namespace MinSumClust

/-- **Lemma 52**, p.51 (PDF p.53), display (29).

Anand et al., *A Constant Approximation for Min-sum k-Clustering*, STOC 2027 submission (manuscript
of November 3, 2026, sha256 103c52a5…), Lemma 52, p.51.

Let `S ⊆ D`, let `T₁, …, T_m ⊆ D` be disjoint nonempty sets, `R_i = S ∩ T_i`, `p_i = |R_i|/|T_i|`,
and let `Z_i ⊆ T_i` be random sets. If for some `a, b ≥ 0`
`Pr[u ∈ Z_i] ≤ a p_i` for every `u ∈ T_i`, and `Pr[u ∈ Z_i, v ∈ Z_j] ≤ b p_i p_j` for every
`i ≠ j`, `u ∈ T_i`, `v ∈ T_j`, then
`E[2 ∑_i d(S, Z_i) + ∑_{i,j} d(Z_i, Z_j)] ≤ (2a + b) cost(S) + (2a + 2b) ∑_i (|S|/|T_i|) d(R_i, T_i)
  + a ∑_i p_i cost(T_i)`.

**Formalization Note.** The random sets are any joint distribution `μ` of `(Z_1, …, Z_m)` with
`Z_i ⊆ T_i` on its support; the sum `∑_{i,j}` includes `i = j`. `d` is any pseudometric. -/
theorem lemma_52 {D : Type} [Fintype D] [DecidableEq D] (d : D → D → ℝ) (hd : IsPseudometric d)
    (S : Finset D) (m : ℕ) (T : Fin m → Finset D) (hT : ∀ i, (T i).Nonempty)
    (hTdisj : ∀ i j, i ≠ j → Disjoint (T i) (T j)) (μ : PMF (Fin m → Finset D))
    (hsupp : ∀ Z ∈ μ.support, ∀ i, Z i ⊆ T i) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h₁ : ∀ i, ∀ u ∈ T i,
      pprob μ (fun Z => u ∈ Z i) ≤ a * (((S ∩ T i).card : ℝ) / (T i).card))
    (h₂ : ∀ i j, i ≠ j → ∀ u ∈ T i, ∀ v ∈ T j,
      pprob μ (fun Z => u ∈ Z i ∧ v ∈ Z j) ≤
        b * (((S ∩ T i).card : ℝ) / (T i).card) * (((S ∩ T j).card : ℝ) / (T j).card)) :
    pexp μ (fun Z => 2 * ∑ i, distSet d S (Z i) + ∑ i, ∑ j, distSet d (Z i) (Z j)) ≤
      (2 * a + b) * cost d S +
        (2 * a + 2 * b) * ∑ i, ((S.card : ℝ) / (T i).card) * distSet d (S ∩ T i) (T i) +
        a * ∑ i, (((S ∩ T i).card : ℝ) / (T i).card) * cost d (T i) := by sorry

end MinSumClust
