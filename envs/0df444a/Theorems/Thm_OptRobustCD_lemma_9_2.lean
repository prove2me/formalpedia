-- Prove2me | Theorems.Thm_OptRobustCD_lemma_9_2
-- name    : OptRobustCD.lemma_9_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T23:51:48.74822+00:00
-- url     : https://prove2.me/theorems/232df6c3-4e0b-48bc-b718-cb64440200f9
-- title:
--   Lemma 9.2 — lifting with the corrupted, degree-truncated graph is ok, and $\|R_Q\|\le O_{d,\lambda,J}(1)$ for maximum degree $\le J$
-- statement:
--   Let $d>0$, $\lambda\in(-1,1)$ with $d\lambda^2>1$, and $(G,\sigma^\star)\sim\mathrm{SBM}(n,d,\lambda)$.
--
--   1. For every $\varepsilon>0$ there is $J_0(\varepsilon)$ such that for every $J\ge J_0$ there is $\eta>0$ such that for every sufficiently large fixed $s$, with high probability, every graph $F$ on $[n]$ with $|E(F)\triangle E(G)|\le\eta n$ satisfies
--   $$\Bigl\|R_{F_J}\frac{A^{(s)}_G\sigma^\star}{(d\lambda)^s}-R_G\frac{A^{(s)}_G\sigma^\star}{(d\lambda)^s}\Bigr\|\le\varepsilon\sqrt n,$$
--   where $F_J$ deletes every edge of $F$ with an endpoint of degree more than $J$.
--   2. Moreover, every graph $Q$ on $[n]$ with maximum degree at most $J$ satisfies $\|R_Q\|\le O_{d,\lambda,J}(1)$.
--
--   It shows the postprocessing of Lemma 5.3 may use the corrupted graph.
--
--   Differences from the source:
--   - encoding: with high probability → the SBM(n,d,λ) probability of the event tends to 1 (Whp); reason: the meaning of the phrase
--   - encoding: for every sufficiently large fixed s → ∃ s₁, ∀ s ⩾ s₁; reason: the meaning of the phrase
--   - encoding: ∥R_Q∥ ⩽ O_{d,λ,J}(1) → ∃ C(d,λ,J), ∀ n, Q, x: ∥R_Q x∥ ⩽ C∥x∥; reason: the meaning of the operator-norm bound
--   - generalization: the 'Moreover' clause for the J of the lemma (J ⩾ J₀) → for every J ∈ ℕ; reason: the bound is deterministic and proved for each J; it specializes to J ⩾ J₀
-- source:
--   Hopkins, Hua, Mohanty, Rajaraman, Steurer, Optimal Robust Community Detection, STOC 2027 submission (manuscript of November 3, 2026, sha256 3d287d5422db7c4a43e74333bda1dbed204af51a25fd9f2c6e875ae03a4dafa1), Lemma 9.2, p.44 (pdf p.46)

import Mathlib
import Definitions.Def_OptRobustCD_Whp
import Definitions.Def_OptRobustCD_nbWalks
import Definitions.Def_OptRobustCD_Lift

namespace OptRobustCD

open scoped Classical

/-- **Lemma 9.2** (Lifting using the corrupted graph is ok). Hopkins, Hua, Mohanty, Rajaraman,
Steurer, *Optimal Robust Community Detection*, STOC 2027 submission (manuscript of November 3,
2026, sha256 3d287d54…), Lemma 9.2, p.44 (pdf p.46).

"For every ε > 0 there is `J_0(ε)` such that for every `J ⩾ J_0` there is η > 0 such that for every
sufficiently large fixed s, with high probability, every graph F on [n] with |E(F)△E(G)| ⩽ ηn
satisfies `∥R_{F_J}(A^{(s)}_G σ⋆/(dλ)^s) − R_G(A^{(s)}_G σ⋆/(dλ)^s)∥ ⩽ ε√n`. Moreover, every graph
Q on [n] with maximum degree at most J satisfies `∥R_Q∥ ⩽ O_{d,λ,J}(1)`."

**Formalization Note.** The setting is that of Lemma 9.1: `(G, σ⋆) ∼ SBM(n, d, λ)` with `dλ² > 1`,
and `d > 0`, `λ ∈ (−1, 1)` (§3.1). "For every sufficiently large fixed s" is `∃ s₁ ∀ s ⩾ s₁`.
`F_J` is the degree cutoff `degCut F J`. The "Moreover" clause is the second conjunct: for every
`J` a constant `C = C(d, λ, J)` with `∥R_Q x∥ ⩽ C∥x∥` for every `n`, every `Q` of maximum degree at
most `J` and every `x`. -/
theorem lemma_9_2 (d lam : ℝ) (hd : 0 < d) (hlam : lam ∈ Set.Ioo (-1 : ℝ) 1)
    (hKS : 1 < d * lam ^ 2) :
    (∀ ε : ℝ, 0 < ε → ∃ J₀ : ℕ, ∀ J : ℕ, J₀ ≤ J → ∃ η : ℝ, 0 < η ∧ ∃ s₁ : ℕ, ∀ s : ℕ, s₁ ≤ s →
      Whp d lam (fun n σ G => ∀ F : SimpleGraph (Fin n), (editDist F G : ℝ) ≤ η * n →
        l2 (fun p => liftR d lam (degCut F J) (sigmaS d lam s G σ) p -
          liftR d lam G (sigmaS d lam s G σ) p) ≤ ε * Real.sqrt n)) ∧
    (∀ J : ℕ, ∃ C : ℝ, ∀ (n : ℕ) (Q : SimpleGraph (Fin n)), (∀ v, Q.degree v ≤ J) →
      ∀ x : Fin n → ℝ, l2 (liftR d lam Q x) ≤ C * l2 x) := by sorry

end OptRobustCD
