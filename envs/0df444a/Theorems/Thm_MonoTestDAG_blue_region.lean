-- Prove2me | Theorems.Thm_MonoTestDAG_blue_region
-- name    : MonoTestDAG.blue_region
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:10:35.697426+00:00
-- url     : https://prove2.me/theorems/9019f2d2-944b-44ec-9f56-9f1994c2e199
-- title:
--   Proof of Theorem 1.1(ii), blue region — $\Omega(n^{c/3-\delta})$ for $c\le3/2$, $c+3d\ge6$
-- statement:
--   There is an absolute $\varepsilon_0>0$ such that the following holds for all $1\le c\le d\le2$ with $c\le3/2$ and $c+3d\ge6$, every $\delta>0$ and every $\varepsilon\in(0,\varepsilon_0]$. There are infinitely many $n$ and transitively reduced $n$-vertex DAGs with
--   $$
--   n^{c-\delta}\le m\le n^{c+\delta},\qquad n^{d-\delta}\le\ell\le n^{d+\delta},
--   $$
--   on which every randomized non-adaptive $\varepsilon$-tester, even with two-sided error, requires $\Omega_{c,d,\delta}(n^{c/3-\delta})$ queries. In this region and on its boundary $u(c,d)=c/3$.
--
--   This is the paper's "stronger statement" (p.35) restricted to the region; the construction is the case of the proof beginning at "Blue region and its boundary" (p.36).
--
--   Differences from the source:
--   - encoding: ε₀ := η₀/128 with η₀ the absolute constant of Lemma 5.3 → an existential absolute ε₀ before c, d; reason: η₀ is itself existential in Lemma 5.3
--   - encoding: "infinitely many n"; Ω with constants depending on the fixed parameters → ∀ N₀ ∃ n ≥ N₀; a constant K after c, d, δ and before ε; reason: Lean form of the page's claim
--   - encoding: Ω(n^{u(c,d)−δ}) → Ω(n^{c/3−δ}); reason: u(c, d) = c/3 in this region, as the proof says
--   - encoding: randomized non-adaptive tester → the structure `Tester`: arbitrary probability space in `Type`, query set a function of the seed, decision a function of the seed and the answers on that set, acceptance event of each input measurable in the seed; reason: the paper's definition in §2.4; a universe-0 probability space loses no tester of the paper; measurability only makes the acceptance probability defined
-- source:
--   Yoshida, Testing Monotonicity of Real-Valued Functions on DAGs, arXiv:2602.15341 (sha256 454609db…), proof of Theorem 1.1(ii), pp.35–37

import Mathlib
import Definitions.Def_MonoTestDAG_Tester
import Definitions.Def_MonoTestDAG_HasExponents

namespace MonoTestDAG

/-- **Proof of Theorem 1.1(ii), blue region and its boundary.** Let `ε₀ := η₀/128`. For
`1 ≤ c ≤ d ≤ 2` with `c ≤ 3/2` and `c + 3d ≥ 6`, every `δ > 0` and every `ε ∈ (0, ε₀]`, there are
infinitely many `n` and transitively reduced `n`-vertex DAGs with `n^{c−δ} ≤ m ≤ n^{c+δ}` and
`n^{d−δ} ≤ ℓ ≤ n^{d+δ}` on which every randomized non-adaptive `ε`-tester, even with two-sided
error, requires `Ω_{c,d,δ}(n^{c/3−δ})` queries (in this region `u(c, d) = c/3`).

Yoshida, *Testing Monotonicity of Real-Valued Functions on DAGs*, arXiv:2602.15341
(sha256 454609db…), proof of Theorem 1.1(ii), blue region, pp.35–37.

**Formalization Note.** This is the paper's "stronger statement" (p.35) restricted to the region.
`ε₀` is existential and absolute (the page's `η₀` is the existential constant of Lemma 5.3).
`Ω_{c,d,δ}` is a constant `K` chosen after `c, d, δ` and before `ε`. "Infinitely many `n`" is
`∀ N₀, ∃ n ≥ N₀`. -/
theorem blue_region :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ c d : ℝ, 1 ≤ c → c ≤ d → d ≤ 2 → c ≤ 3 / 2 → 6 ≤ c + 3 * d →
      ∀ δ : ℝ, 0 < δ → ∃ K : ℝ, 0 < K ∧ ∀ ε : ℝ, 0 < ε → ε ≤ ε₀ → ∀ N₀ : ℕ,
        ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (E : V → V → Prop),
          N₀ ≤ Fintype.card V ∧ 1 ≤ Fintype.card V ∧ IsDAG E ∧ IsTransReduced E ∧
          HasExponents E c d δ ∧
          ∀ (A : Tester V) (q : ℝ), IsTwoSidedTester E ε A → A.QueriesAtMost q →
            K * (Fintype.card V : ℝ) ^ (c / 3 - δ) ≤ q := by sorry

end MonoTestDAG
