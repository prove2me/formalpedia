-- Prove2me | Theorems.Thm_LooseHamHitting_Main_proposition_5_2
-- name    : LooseHamHitting.Main.proposition_5_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T03:19:07.840983+00:00
-- url     : https://prove2.me/theorems/eb2779f3-03df-4e5e-b789-e38bf9020424
-- title:
--   Proposition 5.2 — near-maximal matching entropy forces near-uniform edge marginals
-- statement:
--   Fix $C\ge1$. Let $G$ be a 3-graph on $n$ vertices, $3\mid n$, with $\Delta_1(G)\le Cd(G)$ and $\Delta_2(G)=o(d(G))$ as $n\to\infty$. Let $F$ be a random perfect matching of $G$ with an arbitrary law and $p_e=P[e\in F]$. Then
--   $$H[F]+\frac n6D_{KL}\Big[\Big(\frac{3p_e}n\Big)_{e\in G}\Big\|\,\mathrm{Unif}(G)\Big]\le\frac n3\log d(G)-\frac{2n}3+O_C\Big(\frac n{\log(d(G)/\Delta_2(G))}+\log n\Big),$$
--   and if $H[F]\ge\frac n3\log d(G)-\frac{2n}3-\varepsilon n$ for some $\varepsilon\ge0$, then
--   $$\sum_{e\in G}\Big|p_e-\frac1{d(G)}\Big|=O_C\Big(n\sqrt{\varepsilon+\frac1{\log(d(G)/\Delta_2(G))}+\frac{\log n}n}\Big).$$
--
--   Formally: for every $C\ge1$ there are $K_1,K_2>0$, $\eta>0$ and $N$ such that both bounds hold with constants $K_1$, $K_2$ for every such $G$ and law with $n\ge N$ and $\Delta_2(G)\le\eta\,d(G)$.
--
--   Differences from the source:
--   - encoding: Δ₂(G) = o(d(G)) as n → ∞, conclusions O_C(·) → ∀ C ≥ 1, ∃ K₁ K₂ > 0, ∃ η > 0, ∃ N: n ≥ N and Δ₂ ≤ η d(G) imply both bounds with K₁, K₂; reason: equivalent to the statement over sequences of instances with K₁, K₂ depending only on C (a sequence violating the uniform form for fixed K yields one violating the sequence form)
--   - encoding: relative entropy, possibly +∞ → klDiv in EReal; the left side is computed in EReal; reason: Lean convention; same values
-- source:
--   León, Liu, Hitting time for loose Hamilton cycles in the random hypergraph process, arXiv:2610.29894v1, p. 17, Proposition 5.2

import Mathlib
import Definitions.Def_LooseHamHitting_Main_Hypergraph
import Definitions.Def_LooseHamHitting_Main_Entropy
import Definitions.Def_LooseHamHitting_Main_Marginals

set_option autoImplicit false

open Classical

namespace LooseHamHitting.Main

/-- Proposition 5.2: entropy stability for random perfect matchings. The hypothesis
`Δ₂(G) = o(d(G))` as `n → ∞` and the `O_C(·)` conclusions are encoded uniformly: the constants
`K₁, K₂` depend only on `C`, and the bounds hold once `n ≥ N` and `Δ₂(G) ≤ η d(G)`. -/
theorem proposition_5_2 :
    ∀ C : ℝ, 1 ≤ C → ∃ K₁ K₂ : ℝ, 0 < K₁ ∧ 0 < K₂ ∧ ∃ η : ℝ, 0 < η ∧ ∃ N : ℕ,
      ∀ (β : Type*) (V : Finset β) (G : Finset (Finset β)) (μ : Finset (Finset β) → ℝ) (n : ℕ),
        V.card = n → IsThreeGraph V G → 3 ∣ n → N ≤ n →
        (maxDegree V G : ℝ) ≤ C * avgDegree V G →
        (maxCodegree V G : ℝ) ≤ η * avgDegree V G →
        IsLawOn (perfectMatchings V G) μ →
        ((lawEntropy (perfectMatchings V G) μ id : EReal) +
            (((n : ℝ) / 6 : ℝ) : EReal) *
              klDiv G (fun e => 3 * pmEdgeProb V G μ e / n) (fun _ => 1 / (G.card : ℝ)) ≤
          (((n : ℝ) / 3 * Real.log (avgDegree V G) - 2 * (n : ℝ) / 3 +
            K₁ * ((n : ℝ) / Real.log (avgDegree V G / maxCodegree V G) + Real.log n) : ℝ) :
              EReal)) ∧
        ∀ ε : ℝ, 0 ≤ ε →
          (n : ℝ) / 3 * Real.log (avgDegree V G) - 2 * (n : ℝ) / 3 - ε * n ≤
              lawEntropy (perfectMatchings V G) μ id →
            ∑ e ∈ G, |pmEdgeProb V G μ e - 1 / avgDegree V G| ≤
              K₂ * ((n : ℝ) * Real.sqrt (ε + 1 / Real.log (avgDegree V G / maxCodegree V G) +
                Real.log n / n)) := by sorry

end LooseHamHitting.Main
