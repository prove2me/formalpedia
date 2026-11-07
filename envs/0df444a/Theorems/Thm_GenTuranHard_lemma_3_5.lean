-- Prove2me | Theorems.Thm_GenTuranHard_lemma_3_5
-- name    : GenTuranHard.lemma_3_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:35:30.57469+00:00
-- url     : https://prove2.me/theorems/186db9f3-0386-4e6c-b527-afcb87d9c365
-- title:
--   Lemma 3.5 [AS16, Prop. 2.1] — if $F$ is in a blow-up of $T$, $F$-free graphs have $N(H,T) \le c n^{v(T)-\eta}$
-- statement:
--   Let $T$ and $F$ be graphs with $v(T) > 0$ and $v(F) > 0$, and suppose that $F$ is a subgraph of a blow-up of $T$. Then there exist constants $c = c(T, F) > 0$ and $\eta = \eta(T, F) \in (0, v(T))$ such that every $n$-vertex $F$-free graph $H$ satisfies
--
--   $$
--   N(H, T) \le c\, n^{v(T) - \eta}.
--   $$
--
--   This result of Alon and Shikhelman bounds the number of copies of $K_k$ in the $\mathcal F$-free part of the reduction (proof of Lemma 4.8).
--
--   Differences from the source:
--   - encoding: N(H, T), the number of copies of T in H → Mathlib copyCount: subgraphs of H isomorphic to T; reason: the same count: copies with different vertex sets or edge sets are different subgraphs
--   - encoding: n^{v(T)−η} → (n : ℝ) ^ ((v(T) : ℝ) − η) (Real.rpow); reason: the real power; for n ≥ 1 it is the usual power
--   - encoding: “F is a subgraph of a blow-up of T” → F has a copy in blowUp T s for some s with all cluster sizes positive; reason: the paper's definition (pp.3, 5)
-- source:
--   Chen, He, Li, Ma, Xie, NP-hardness of additive approximation for generalized Turán problems, arXiv:2610.16358 (sha256 dc85633a…), Lemma 3.5, p.12 (from [AS16, Proposition 2.1])

import Mathlib
import Definitions.Def_GenTuranHard_blowUp

set_option autoImplicit false

namespace GenTuranHard

/-- **Lemma 3.5** ([AS16, Proposition 2.1]; Chen, He, Li, Ma, Xie, arXiv:2610.16358, sha256 dc85633a…,
Lemma 3.5, p.12). Let `T` and `F` be graphs with `v(T) > 0` and `v(F) > 0`, and suppose that `F` is a
subgraph of a blow-up of `T`. Then there are constants `c = c(T, F) > 0` and `η = η(T, F) ∈ (0, v(T))`
such that every `n`-vertex `F`-free graph `H` satisfies `N(H, T) ≤ c·n^{v(T)−η}`.

**Formalization Note** Cited from Alon–Shikhelman; posed, not assumed. `N(H, T)` is `copyCount`; the
power is `Real.rpow`. The constants are chosen before `n` and `H`. -/
theorem lemma_3_5 {W U : Type} [Fintype W] [Fintype U] (T : SimpleGraph W) (F : SimpleGraph U)
    (hT : 0 < Fintype.card W) (hF : 0 < Fintype.card U) (hFT : InBlowUp F T) :
    ∃ c : ℝ, 0 < c ∧ ∃ η : ℝ, 0 < η ∧ η < Fintype.card W ∧
      ∀ (n : ℕ) (H : SimpleGraph (Fin n)), F.Free H →
        (H.copyCount T : ℝ) ≤ c * (n : ℝ) ^ ((Fintype.card W : ℝ) - η) := by sorry

end GenTuranHard
