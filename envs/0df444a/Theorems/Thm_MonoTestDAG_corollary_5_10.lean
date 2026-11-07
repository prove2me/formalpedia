-- Prove2me | Theorems.Thm_MonoTestDAG_corollary_5_10
-- name    : MonoTestDAG.corollary_5_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:10:30.025739+00:00
-- url     : https://prove2.me/theorems/85c67836-278e-41a1-be89-91816ce6a30b
-- title:
--   Corollary 5.10 — exponent form for the red region
-- statement:
--   Fix constants $c,d$ with $1\le c\le d$ and $c+3d<6$. For every $\delta>0$ and every sufficiently small constant $\varepsilon>0$, there are infinitely many $n$ and transitively reduced $n$-vertex DAGs with
--   $$
--   n^{c-\delta}\le m\le n^{c+\delta},\qquad n^{d-\delta}\le\ell\le n^{d+\delta},
--   $$
--   such that every randomized non-adaptive $\varepsilon$-tester, even with two-sided error, requires
--   $$
--   \Omega_{c,d,\delta}\Bigl(n^{-\delta}\cdot\frac{\sqrt{m\ell}}{\varepsilon n}\Bigr)
--   $$
--   queries.
--
--   Differences from the source:
--   - generalization: "for every sufficiently small ε", after the other parameters → an absolute threshold ε₁ before them; reason: the proof of Theorem 1.1(ii) uses this uniformity (p.36); it specializes to the printed order
--   - encoding: "infinitely many n"; Ω with constants depending on the fixed parameters → ∀ N₀ ∃ n ≥ N₀; a constant K after c, d, δ and before ε; reason: Lean form of the page's claim
--   - encoding: randomized non-adaptive tester → the structure `Tester`: arbitrary probability space in `Type`, query set a function of the seed, decision a function of the seed and the answers on that set, acceptance event of each input measurable in the seed; reason: the paper's definition in §2.4; a universe-0 probability space loses no tester of the paper; measurability only makes the acceptance probability defined
-- source:
--   Yoshida, Testing Monotonicity of Real-Valued Functions on DAGs, arXiv:2602.15341 (sha256 454609db…), Corollary 5.10, p.34

import Mathlib
import Definitions.Def_MonoTestDAG_Tester
import Definitions.Def_MonoTestDAG_HasExponents

namespace MonoTestDAG

/-- **Corollary 5.10 (Exponent form for the red region).** Fix `c, d` with `1 ≤ c ≤ d` and
`c + 3d < 6`. For every `δ > 0` and every sufficiently small constant `ε > 0`, there are infinitely
many `n` and transitively reduced `n`-vertex DAGs with `n^{c−δ} ≤ m ≤ n^{c+δ}` and
`n^{d−δ} ≤ ℓ ≤ n^{d+δ}` such that every randomized non-adaptive `ε`-tester with two-sided error
requires `Ω_{c,d,δ}(n^{−δ} · √(mℓ)/(εn))` queries.

Yoshida, *Testing Monotonicity of Real-Valued Functions on DAGs*, arXiv:2602.15341
(sha256 454609db…), Corollary 5.10, p.34.

**Formalization Note.** "Infinitely many `n`" is `∀ N₀, ∃ n ≥ N₀`. `Ω_{c,d,δ}` is a constant `K`
chosen after `c, d, δ` and before `ε`. The threshold `ε₁` is absolute, chosen before `c, d, δ`: its
proof uses Theorem 5.9 with the same absolute `η₀`, which is how the proof of Theorem 1.1(ii) applies
it (p.36). -/
theorem corollary_5_10 :
    ∃ ε₁ : ℝ, 0 < ε₁ ∧ ∀ c d : ℝ, 1 ≤ c → c ≤ d → c + 3 * d < 6 → ∀ δ : ℝ, 0 < δ →
      ∃ K : ℝ, 0 < K ∧ ∀ ε : ℝ, 0 < ε → ε < ε₁ → ∀ N₀ : ℕ,
        ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (E : V → V → Prop),
          N₀ ≤ Fintype.card V ∧ 1 ≤ Fintype.card V ∧ IsDAG E ∧ IsTransReduced E ∧
          HasExponents E c d δ ∧
          ∀ (A : Tester V) (q : ℝ), IsTwoSidedTester E ε A → A.QueriesAtMost q →
            K * ((Fintype.card V : ℝ) ^ (-δ) *
              (Real.sqrt ((numTR E : ℝ) * (numTC E : ℝ)) / (ε * (Fintype.card V : ℝ)))) ≤ q := by sorry

end MonoTestDAG
