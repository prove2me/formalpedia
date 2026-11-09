-- Prove2me | Theorems.Thm_L22EigEst_lemma_4_7
-- name    : L22EigEst.lemma_4_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T06:27:04.396204+00:00
-- url     : https://prove2.me/theorems/574dfdfb-3b22-4e93-a649-cabde74172e2
-- title:
--   Lemma 4.7 — under E3, E4, $\|SA'S^\top-M\|_2\le\varepsilon\|A\|_F$ with $O(\log^{1.5}(1/\varepsilon)/\varepsilon^4)$ queries, w.p. $\ge0.95$
-- statement:
--   For every $c_3>0$ there is $c_0$ such that for every $c\ge c_0$ there is a constant $C$ with the following property. Let $A\in\mathbb R^{n\times n}$ be symmetric, $\varepsilon\in(0,1/4)$, $s=\lceil c\log(1/\varepsilon)/\varepsilon^2\rceil$, and suppose $A$ satisfies (1). Fix a sampling pattern $\delta$, with $S=\mathrm{diag}(\delta_i/\sqrt{p_i})$, $p_i=s\|A_i\|_2^2/\|A\|_F^2$, such that
--
--   1. (E3) $S$ samples at most $c_3s$ rows, and
--   2. (E4) $\max_i\sum_{j\ne i}(SA'S^\top)_{ij}^2\le1000\,\varepsilon^2\|A\|_F^2/(c\log(1/\varepsilon))$.
--
--   Let $q=1/\sqrt{\log(1/\varepsilon)}$, draw $\xi_{ij}\sim\mathrm{Ber}(q)$ independently for $i<j$, and form $M$ from $SA'S^\top$ by (3). Then with probability at least $0.95$ over $\xi$, both
--
--   $$\|SA'S^\top-M\|_2\le\varepsilon\|A\|_F$$
--
--   and the number of entries queried to form $M$ (the sampled diagonal entries and the sampled pairs with $\xi_{ij}=1$) is at most $C\log^{1.5}(1/\varepsilon)/\varepsilon^4$.
--
--   Keeping only a $1/\sqrt{\log(1/\varepsilon)}$ fraction of the off-diagonal entries is what brings the query count from $O(\log^2(1/\varepsilon)/\varepsilon^4)$ down to $O(\log^{1.5}(1/\varepsilon)/\varepsilon^4)$.
--
--   Differences from the source:
--   - generalization: E3 "for some constant c3" → every c₃ > 0, with c₀ and C depending on c₃; reason: the proof works for any c₃ (only log(c₃s) = O(log(1/ε)) and |S|² ≤ c₃²s² enter); the paper's c₃ (≥ 20, Claim 4.5) is one of them
--   - generalization: "If c is a sufficiently large constant" → every c ≥ c₀; reason: "sufficiently large" is a lower bound on c
--   - reading: "with probability at least 0.95 over M, ∥SA′S⊺ − M∥2 ≤ ε∥A∥F, and forming M requires querying at most O(…) entries" → one event over ξ containing both conclusions, with the O(·) an explicit C chosen after c₃, c and before n, A, ε, δ; reason: the proof unions the two 0.99 events (p.24)
--   - reading: Definition 4.2: "For ε ∈ (0, 1)" → ε ∈ (0, 1/4); reason: the events concern the sampling matrix of Algorithm 1, whose accuracy parameter is ε ∈ (0, 1/4) (Algorithm 1, Theorem 5); on (0, 1) Lemma 4.3 fails (A = I₂, ε close to 1, s = 1)
--   - encoding: S drawn as in Algorithm 1 and conditioned on E3, E4 → a fixed pattern δ satisfying E3 and E4, the probability over the coins ξ only; reason: the lemma conditions on S; ξ is independent of S
--   - encoding: ξ_ij ∼ Ber(q) for i < j, probability over M → product Bernoulli weights over the pairs i < j (bernProb on Pair n); reason: a finite product of Bernoulli laws
--   - encoding: S ∈ ℝ^{s×n} and M ∈ ℝ^{s×s} → their n × n views (sampMat, subMat); reason: the two views differ by zero rows and columns, which change no spectral norm (p.9, p.15)
-- source:
--   Menand, Waingarten, Dimension-Free ℓ₂²-Sampling Algorithms for Eigenvalue Estimation, STOC 2027 submission (manuscript sha256 b1f6adce…), Lemma 4.7 and Definition 4.2 (Events E3, E4), pp.13–14

import Definitions.Def_L22EigEst_BoundedRowNorm
import Definitions.Def_L22EigEst_bernW
import Definitions.Def_L22EigEst_sampMat
import Definitions.Def_L22EigEst_zeroed
import Definitions.Def_L22EigEst_subMat
import Definitions.Def_L22EigEst_eventE4
import Definitions.Def_WainwrightHDS_EigPert_opNorm2

open WainwrightHDS.EigPert

namespace L22EigEst

/-- **Lemma 4.7** (p.14), Menand, Waingarten, *Dimension-Free ℓ₂²-Sampling Algorithms for Eigenvalue Estimation*, STOC 2027
submission (manuscript sha256 b1f6adce…): "Let A ∈ ℝ^{n×n} satisfy Definition 3.1, and let S and M be as in Algorithm 1 with
q = 1/√log(1/ε). If c is a sufficiently large constant and S satisfies events E3 and E4, then with
probability at least 0.95 over M, ∥SA′S⊺ − M∥2 ≤ ε∥A∥F, and forming M requires querying at most
O(log^1.5(1/ε)/ε⁴) entries of A." Event E3 (Definition 4.2, p.13): "The sampling matrix samples at
most c3s many rows for some constant c3."

**Formalization Note.** `s = sParam c ε`, `S = sampMat (rowProb s A) δ` for a fixed pattern `δ` (the
lemma conditions on `S`), `A′ = zeroed A ε`, `M = subMat (SA′S) q ξ` with `ξ_ij ∼ Ber(q)` independent
for `i < j`; the probability over `ξ` is a finite sum (`bernProb` on `Pair n`). E3 is
`|S| ≤ c₃ s`, E4 is `eventE4`. The statement holds for every `c₃ > 0` and every `c ≥ c₀(c₃)`;
the O(·) constant `C` depends on `c₃` and `c` only. One event contains both conclusions. The query
count is `queries δ ξ` (sampled diagonal entries plus sampled pairs with `ξ_ij = 1`).
`ε ∈ (0, 1/4)`, Algorithm 1's domain. -/
theorem lemma_4_7 :
    ∀ c₃ : ℝ, 0 < c₃ → ∃ c₀ : ℝ, ∀ c : ℝ, c₀ ≤ c → ∃ C : ℝ,
      ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) (_hA : A.IsHermitian) (ε : ℝ) (δ : Fin n → Bool),
      0 < ε → ε < 1 / 4 → BoundedRowNorm (sParam c ε) A →
      (sampCount δ : ℝ) ≤ c₃ * sParam c ε → eventE4 c ε A δ →
      (0.95 : ℝ) ≤ bernProb (fun _ : Pair n => qParam ε)
        (fun ξ =>
          opNorm2 (sampMat (rowProb (sParam c ε) A) δ * zeroed A ε *
              sampMat (rowProb (sParam c ε) A) δ -
            subMat (sampMat (rowProb (sParam c ε) A) δ * zeroed A ε *
              sampMat (rowProb (sParam c ε) A) δ) (qParam ε) ξ) ≤ ε * frob A ∧
          (queries δ ξ : ℝ) ≤ C * Real.log (1 / ε) ^ (3 / 2 : ℝ) / ε ^ 4) := by sorry

end L22EigEst
