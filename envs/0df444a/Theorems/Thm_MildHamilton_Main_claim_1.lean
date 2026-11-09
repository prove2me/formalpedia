-- Prove2me | Theorems.Thm_MildHamilton_Main_claim_1
-- name    : MildHamilton.Main.claim_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T09:52:26.711344+00:00
-- url     : https://prove2.me/theorems/9f374982-d667-4345-b73a-15b700536c1d
-- title:
--   Claim 1 (in the proof of Lemma 3.1), p. 6 — one short connection survives deletion (corrected: 0 < ∆)
-- statement:
--   There are absolute constants $C_0,C>0$ such that the following holds under all hypotheses of Lemma 3.1 with this $C$, together with $\Delta>0$. Put $\ell=C_0\gamma^{-1}\log(2|R|)$. For every $I\subseteq[k]$ and $U\subseteq R$ with
--
--   $$|U|\le(2\ell-3)(|I|-1),$$
--
--   there is some $i\in I$ and an $a_i$–$b_i$ path of length at most $\ell$ whose internal vertices are in $R\setminus U$.
--
--   This is exactly the vertex-cover hypothesis of Haxell's theorem for the hypergraph of short connecting paths.
--
--   Differences from the source:
--   - correction: no lower bound on Δ = Δ(G[R]) → the hypothesis 0 < Δ(G[R]); reason: the printed statement is false at Δ = 0: take five isolated vertices, R three of them, k = 1, (a_1, b_1) the other two, p = 0, γ = 1, β = 1/2; every printed hypothesis holds and no a_1–b_1 path exists; the proof divides by βΔ on p. 7
--   - encoding: C_0 sufficiently large and C sufficiently large compared with C_0 → ∃ C₀ C > 0 chosen before the graph; reason: the constants are absolute; the hypotheses only get stronger as C grows, so the claim for one C gives every larger C
-- source:
--   Alp Muyesser, STOC 2027 submission #233 (October 2026), Claim 1, in the proof of Lemma 3.1, p. 6

import Mathlib
import Definitions.Def_MildHamilton_Main_Spectral

namespace MildHamilton.Main

open Classical in
/-- Claim 1, in the proof of Lemma 3.1 (Muyesser, STOC 2027 submission #233, p. 6), with
`ℓ = C₀ γ⁻¹ log(2|R|)` and all hypotheses of Lemma 3.1, corrected by `0 < Δ(G[R])`. -/
theorem claim_1 :
    ∃ C₀ C : ℝ, 0 < C₀ ∧ 0 < C ∧ ∀ (V : Type) [Fintype V] (G : SimpleGraph V) (R : Finset V) (p γ β : ℝ)
      (k : ℕ) (a b : Fin k → V) (T : Finset V),
      3 ≤ R.card → IsCutDense (G.induce (R : Set V)) p →
      0 < inducedMaxDegree G R →
      0 < γ → γ ≤ 1 → γ * (inducedMaxDegree G R : ℝ) ≤ p * (R.card : ℝ) →
      (∀ i, a i ∉ R ∧ b i ∉ R) →
      T = Finset.univ.image a ∪ Finset.univ.image b →
      0 < β → β < 1 →
      (∀ x : V, (Finset.univ.filter fun i => a i = x).card +
        (Finset.univ.filter fun i => b i = x).card ≤ 10) →
      (∀ x ∈ T, β * (inducedMaxDegree G R : ℝ) ≤ (nbrCount G x R : ℝ)) →
      (∀ v ∈ R, (nbrCount G v T : ℝ) ≤
        β * γ ^ 2 * (inducedMaxDegree G R : ℝ) / (C * Real.log (2 * (R.card : ℝ)))) →
      ∀ (I : Finset (Fin k)) (U : Finset V), U ⊆ R →
        (U.card : ℝ) ≤ (2 * (C₀ * γ⁻¹ * Real.log (2 * (R.card : ℝ))) - 3) * ((I.card : ℝ) - 1) →
        ∃ i ∈ I, ∃ P : G.Walk (a i) (b i), P.IsPath ∧
          (P.length : ℝ) ≤ C₀ * γ⁻¹ * Real.log (2 * (R.card : ℝ)) ∧
          internalVerts P ⊆ R \ U := by sorry

end MildHamilton.Main
