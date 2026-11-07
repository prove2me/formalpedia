-- Prove2me | Theorems.Thm_MonoTestDAG_lemma_5_5
-- name    : MonoTestDAG.lemma_5_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:11:08.210072+00:00
-- url     : https://prove2.me/theorems/de06767b-3d86-42b4-ad68-71b9ca9ff2c2
-- title:
--   Lemma 5.5 — planting with deterministic padding
-- statement:
--   Assume the hypotheses of Lemma 5.4. Fix a constant $A\ge0$, let $H$ be any DAG on at most $ATn_{\mathrm{base}}$ vertices, and let $G$ be the disjoint union of $G^{(T)}$ and $H$. For every $\varepsilon>0$ and every integer $1\le T\le\varepsilon_\star/(2(A+1)\varepsilon)$, every randomized non-adaptive $\varepsilon$-tester on $G$, even with two-sided error, requires $\Omega(Tq_0)$ queries. The hidden constant is absolute and independent of $A$.
--
--   Differences from the source:
--   - reading: distributions over functions → `PMF` on functions; reason: for a non-discrete D the average acceptance probability needs joint measurability the paper never states; every distribution the paper constructs is finitely supported
--   - encoding: randomized non-adaptive tester → the structure `Tester`: arbitrary probability space in `Type`, query set a function of the seed, decision a function of the seed and the answers on that set, acceptance event of each input measurable in the seed; reason: the paper's definition in §2.4; a universe-0 probability space loses no tester of the paper; measurability only makes the acceptance probability defined
--   - encoding: "let h_H be any fixed monotone function on H" → no binder; reason: the conclusion does not mention h_H, and a monotone function exists on every DAG
--   - encoding: Ω(Tq₀), absolute and independent of A → a constant c > 0 before A; reason: the printed order of the constants
-- source:
--   Yoshida, Testing Monotonicity of Real-Valued Functions on DAGs, arXiv:2602.15341 (sha256 454609db…), Lemma 5.5, p.29

import Mathlib
import Definitions.Def_MonoTestDAG_Tester
import Definitions.Def_MonoTestDAG_transcript
import Definitions.Def_MonoTestDAG_copyEdge

namespace MonoTestDAG

/-- **Lemma 5.5 (Planting in a uniformly random copy with deterministic padding).** Assume the
hypotheses of Lemma 5.4 (a DAG `G₀` on `n_base` vertices, `ε⋆ > 0`, `q₀ ≥ 1`, distributions
`D⁺`, `D⁻` with (i)–(iii)). Fix a constant `A ≥ 0` and let `H` be any DAG on at most `A T n_base`
vertices. Let `G` be the disjoint union of `G^{(T)}` and `H`. For every `ε > 0` and every integer
`1 ≤ T ≤ ε⋆/(2(A + 1)ε)`, every randomized non-adaptive `ε`-tester for monotonicity on `G` with
two-sided error requires `Ω(T q₀)` queries; the hidden constant is absolute and independent of `A`.

Yoshida, *Testing Monotonicity of Real-Valued Functions on DAGs*, arXiv:2602.15341
(sha256 454609db…), Lemma 5.5, p.29.

**Formalization Note.** `Ω(T q₀)` is `c · T · q₀` with `c > 0` chosen before `A`. The paper also
fixes a monotone function `h_H` on `H`, used only in the proof; the conclusion does not mention it
and monotone functions exist on every DAG, so it is not a binder. -/
theorem lemma_5_5 :
    ∃ c : ℝ, 0 < c ∧ ∀ (A : ℝ), 0 ≤ A → ∀ {V₀ : Type} [Fintype V₀] [DecidableEq V₀]
      (E₀ : V₀ → V₀ → Prop) (Dp Dm : PMF (V₀ → ℝ)) (εs : ℝ) (q₀ : ℕ), IsDAG E₀ → 0 < εs →
      1 ≤ q₀ → (∀ f ∈ Dp.support, IsMonotone E₀ f) →
      (9 / 10 : ENNReal) ≤ Dm.toOuterMeasure {f | IsFar E₀ εs f} →
      (∀ Q : Finset V₀, Q.card ≤ q₀ → trTV Dp Dm Q ≤ 1 / 20) →
      ∀ ε : ℝ, 0 < ε → ∀ T : ℕ, 1 ≤ T → (T : ℝ) ≤ εs / (2 * (A + 1) * ε) →
      ∀ {H : Type} [Fintype H] [DecidableEq H] (EH : H → H → Prop), IsDAG EH →
      (Fintype.card H : ℝ) ≤ A * (T : ℝ) * (Fintype.card V₀ : ℝ) →
      ∀ (Tst : Tester ((Fin T × V₀) ⊕ H)) (q : ℝ),
        IsTwoSidedTester (unionEdge (copyEdge E₀ T) EH) ε Tst →
        Tst.QueriesAtMost q → c * (T : ℝ) * (q₀ : ℝ) ≤ q := by sorry

end MonoTestDAG
