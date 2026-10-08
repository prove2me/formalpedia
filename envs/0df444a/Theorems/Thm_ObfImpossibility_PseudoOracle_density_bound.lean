-- Prove2me | Theorems.Thm_ObfImpossibility_PseudoOracle_density_bound
-- name    : ObfImpossibility.PseudoOracle.density_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T10:28:16.848273+00:00
-- url     : https://prove2.me/theorems/7c3536be-4e0d-4284-8078-084daae3b5e1
-- title:
--   End of App. B, p. A:45 — the set $\mathcal G$ of $G$ violating (7) has density smaller than $K^{-\delta}$
-- statement:
--   There is $\delta_0>0$ such that for every $0<\delta\le\delta_0$ there is $K_0$ with the following property. For all $K\ge K_0$ and $L\ge K^2$ and every distinguisher $D$ making at most $K^\delta$ oracle queries, let $\mathcal G$ be the set of injective $G:[K]\to[L]$ with
--   $$\Big|\Pr_{x\in[K]}\big[D^G(G(x))=1\big]-\Pr_{y\in[L]}\big[D^G(y)=1\big]\Big|>\frac1{K^\delta}.$$
--   Then the fraction of injective functions $[K]\to[L]$ that lie in $\mathcal G$ is smaller than $K^{-\delta}$.
--
--   This is the sentence that closes Appendix B. It is weaker than Lemma B.1, which bounds the same fraction by $2^{-K^\delta}$; the counting bound of Claim B.1.2 supports the stronger conclusion once $1-7\delta>\delta$.
--
--   **Formalization Note** The fraction is $|\mathcal G|$ divided by the number of embeddings `Fin K ↪ Fin L`. The existence of $\delta_0$ renders the paper's "sufficiently small $\delta$".
-- source:
--   Barak et al., On the (Im)possibility of Obfuscating Programs, J. ACM 59(2) (2012), author's copy, p. A:45, Appendix B, last paragraph (density of 𝒢)

import Mathlib
import Definitions.Def_ObfImpossibility_PseudoOracle_Setting

namespace ObfImpossibility.PseudoOracle

/-- The density bound, p. A:45: for every sufficiently small `δ > 0`, for all large `K`,
all `L ≥ K²` and every `D` making at most `K^δ` queries, the set `𝒢` of injective
`G : [K] → [L]` violating (7) has density smaller than `K^{-δ}`. -/
theorem density_bound :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ → ∃ K₀ : ℕ, ∀ K L : ℕ, K₀ ≤ K → K ^ 2 ≤ L →
      ∀ D : Fin L → QTree K L, (∀ y, ((D y).depth : ℝ) ≤ (K : ℝ) ^ δ) →
        ((Finset.univ.filter fun G : Fin K ↪ Fin L =>
            1 / (K : ℝ) ^ δ < |prX D G - prY D G|).card : ℝ) /
          (Fintype.card (Fin K ↪ Fin L) : ℝ) < (K : ℝ) ^ (-δ) := by sorry

end ObfImpossibility.PseudoOracle
