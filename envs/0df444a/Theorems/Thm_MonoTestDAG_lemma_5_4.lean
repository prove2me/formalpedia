-- Prove2me | Theorems.Thm_MonoTestDAG_lemma_5_4
-- name    : MonoTestDAG.lemma_5_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:10:39.112188+00:00
-- url     : https://prove2.me/theorems/aec6940d-c57a-4008-8d63-bd285d42b2d8
-- title:
--   Lemma 5.4 — planting in a uniformly random copy
-- statement:
--   Let $G_0$ be a DAG on $n_{\mathrm{base}}$ vertices with distributions $D^\pm$ over functions on $G_0$ such that, for some $\varepsilon_\star>0$ and $q_0\ge1$: (i) $D^+$ is supported on monotone functions; (ii) $f\sim D^-$ is $\varepsilon_\star$-far with probability at least $9/10$; (iii) every $Q\subseteq V(G_0)$ with $|Q|\le q_0$ has $\mathrm{TV}(\mathrm{Tr}(D^+,Q),\mathrm{Tr}(D^-,Q))\le1/20$. Let $G^{(T)}$ be the disjoint union of $T$ copies of $G_0$. For every $\varepsilon>0$ and every integer $1\le T\le\varepsilon_\star/(2\varepsilon)$, every randomized non-adaptive $\varepsilon$-tester on $G^{(T)}$, even with two-sided error, requires $\Omega(Tq_0)$ queries, with an absolute hidden constant.
--
--   Differences from the source:
--   - reading: distributions over functions → `PMF` on functions; reason: for a non-discrete D the average acceptance probability needs joint measurability the paper never states; every distribution the paper constructs is finitely supported
--   - encoding: randomized non-adaptive tester → the structure `Tester`: arbitrary probability space in `Type`, query set a function of the seed, decision a function of the seed and the answers on that set, acceptance event of each input measurable in the seed; reason: the paper's definition in §2.4; a universe-0 probability space loses no tester of the paper; measurability only makes the acceptance probability defined
--   - encoding: Ω(Tq₀), absolute → a constant c > 0 before every other object, with c·T·q₀ ≤ q; reason: Lean form of the page's absolute constant
-- source:
--   Yoshida, Testing Monotonicity of Real-Valued Functions on DAGs, arXiv:2602.15341 (sha256 454609db…), Lemma 5.4, pp.28–29

import Mathlib
import Definitions.Def_MonoTestDAG_Tester
import Definitions.Def_MonoTestDAG_transcript
import Definitions.Def_MonoTestDAG_copyEdge

namespace MonoTestDAG

/-- **Lemma 5.4 (Planting in a uniformly random copy).** Let `G₀` be a DAG on `n_base` vertices
with distributions `D⁺`, `D⁻` over functions on `G₀` such that, for some `ε⋆ > 0` and `q₀ ≥ 1`,
(i) `D⁺` is supported on monotone functions; (ii) `f ∼ D⁻` is `ε⋆`-far with probability at least
`9/10`; (iii) every query set `Q ⊆ V(G₀)` with `|Q| ≤ q₀` has
`TV(Tr(D⁺, Q), Tr(D⁻, Q)) ≤ 1/20`. Let `G^{(T)}` be the disjoint union of `T` copies of `G₀`.
For every `ε > 0` and every integer `1 ≤ T ≤ ε⋆/(2ε)`, every randomized non-adaptive `ε`-tester
for monotonicity on `G^{(T)}` with two-sided error requires `Ω(T q₀)` queries, with an absolute
hidden constant.

Yoshida, *Testing Monotonicity of Real-Valued Functions on DAGs*, arXiv:2602.15341
(sha256 454609db…), Lemma 5.4, pp.28–29.

**Formalization Note.** `Ω(T q₀)` is `c · T · q₀` for an absolute `c > 0` chosen first; the copies
are indexed by `Fin T`. -/
theorem lemma_5_4 :
    ∃ c : ℝ, 0 < c ∧ ∀ {V₀ : Type} [Fintype V₀] [DecidableEq V₀] (E₀ : V₀ → V₀ → Prop)
      (Dp Dm : PMF (V₀ → ℝ)) (εs : ℝ) (q₀ : ℕ), IsDAG E₀ → 0 < εs → 1 ≤ q₀ →
      (∀ f ∈ Dp.support, IsMonotone E₀ f) →
      (9 / 10 : ENNReal) ≤ Dm.toOuterMeasure {f | IsFar E₀ εs f} →
      (∀ Q : Finset V₀, Q.card ≤ q₀ → trTV Dp Dm Q ≤ 1 / 20) →
      ∀ ε : ℝ, 0 < ε → ∀ T : ℕ, 1 ≤ T → (T : ℝ) ≤ εs / (2 * ε) →
      ∀ (A : Tester (Fin T × V₀)) (q : ℝ), IsTwoSidedTester (copyEdge E₀ T) ε A →
        A.QueriesAtMost q → c * (T : ℝ) * (q₀ : ℝ) ≤ q := by sorry

end MonoTestDAG
