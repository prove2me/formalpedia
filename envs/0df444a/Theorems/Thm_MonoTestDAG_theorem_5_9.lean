-- Prove2me | Theorems.Thm_MonoTestDAG_theorem_5_9
-- name    : MonoTestDAG.theorem_5_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:10:58.10457+00:00
-- url     : https://prove2.me/theorems/bedf048d-3ff1-45f7-86b3-4ad9c144ab30
-- title:
--   Theorem 5.9 — lower bound matching the $\ell$-dependent tester
-- statement:
--   Fix integers $r\ge t\ge1$. For all sufficiently large $P$, let $s=P^t$ and $n_0=\Theta_{r,t}(P^{r+t+2})$. Let $D$ be any integer with $1\le D\le s$. Then for every sufficiently small $\varepsilon>0$ there are transitively reduced DAGs $G$ with
--   $$
--   n=\Theta_{r,t}(Tn_0D),\quad m=\Theta_{r,t}(Tn_0s),\quad \ell=\Theta_{r,t}(Tn_0sD^2),\quad T=\Theta_{r,t}(1/\varepsilon),
--   $$
--   such that every randomized non-adaptive $\varepsilon$-tester on $G$, even with two-sided error, makes at least
--   $$
--   \Omega_{r,t}\Bigl(\frac1{\log n}\cdot\frac{\sqrt{m\ell}}{\varepsilon n}\Bigr)
--   $$
--   queries.
--
--   Differences from the source:
--   - generalization: "for every sufficiently small ε", after the other parameters → an absolute threshold ε₁ before them; reason: the proof of Theorem 1.1(ii) uses this uniformity (p.36); it specializes to the printed order
--   - reading: n₀ is "the size of each bipartition class in the graph from Lemma 5.3" → an existential n₀ with the stated Θ, chosen before D and ε; reason: the graph of Lemma 5.3 is itself existential, and the statement uses only this size
--   - encoding: Θ_{r,t}, Ω_{r,t} → constants C ≥ 1 and c > 0 after r, t, before P, D, ε; reason: Lean form of the page's constants
--   - encoding: log with no base → `Real.log`; reason: the base is absorbed by c
--   - encoding: randomized non-adaptive tester → the structure `Tester`: arbitrary probability space in `Type`, query set a function of the seed, decision a function of the seed and the answers on that set, acceptance event of each input measurable in the seed; reason: the paper's definition in §2.4; a universe-0 probability space loses no tester of the paper; measurability only makes the acceptance probability defined
-- source:
--   Yoshida, Testing Monotonicity of Real-Valued Functions on DAGs, arXiv:2602.15341 (sha256 454609db…), Theorem 5.9, p.33

import Mathlib
import Definitions.Def_MonoTestDAG_Tester
import Definitions.Def_MonoTestDAG_numTC
import Definitions.Def_MonoTestDAG_numTR

namespace MonoTestDAG

/-- **Theorem 5.9 (Lower bound matching the `ℓ`-dependent tester, even with two-sided error).** Fix
integers `r ≥ t ≥ 1`. For all sufficiently large `P`, let `s = P^t` and `n₀ = Θ_{r,t}(P^{r+t+2})`.
Let `1 ≤ D ≤ s`. For every sufficiently small `ε > 0` there are transitively reduced DAGs `G` with
`n = Θ_{r,t}(T n₀ D)`, `m = Θ_{r,t}(T n₀ s)`, `ℓ = Θ_{r,t}(T n₀ s D²)`, `T = Θ_{r,t}(1/ε)`, such that
every randomized non-adaptive `ε`-tester on `G` with two-sided error makes at least
`Ω_{r,t}((1/log n) · √(mℓ)/(εn))` queries.

Yoshida, *Testing Monotonicity of Real-Valued Functions on DAGs*, arXiv:2602.15341
(sha256 454609db…), Theorem 5.9, p.33.

**Formalization Note.** The `Θ_{r,t}`, `Ω_{r,t}` are constants `C`, `c` depending on `r, t` only,
chosen before `P`, `D`, `ε`. `n₀` is existential, chosen before `D` and `ε`; on the page it is the
class size of the graph of Lemma 5.3, whose only stated property is this size. The threshold `ε₁`
for "sufficiently small" is absolute (the proof takes `ε < ε⋆/2 = η₀/16`), chosen before `r, t`, as
the proof of Theorem 1.1(ii) uses it (p.36). `log` is the natural logarithm. -/
theorem theorem_5_9 :
    ∃ ε₁ : ℝ, 0 < ε₁ ∧ ∀ r t : ℕ, 1 ≤ t → t ≤ r →
      ∃ C c : ℝ, 1 ≤ C ∧ 0 < c ∧ ∃ P₀ : ℕ, ∀ P : ℕ, P₀ ≤ P →
        ∃ n₀ : ℕ, (P : ℝ) ^ (r + t + 2) / C ≤ (n₀ : ℝ) ∧ (n₀ : ℝ) ≤ C * (P : ℝ) ^ (r + t + 2) ∧
        ∀ D : ℕ, 1 ≤ D → D ≤ P ^ t → ∀ ε : ℝ, 0 < ε → ε < ε₁ →
          ∃ (T : ℕ) (V : Type) (_ : Fintype V) (_ : DecidableEq V) (E : V → V → Prop),
            1 / (C * ε) ≤ (T : ℝ) ∧ (T : ℝ) ≤ C / ε ∧ IsDAG E ∧ IsTransReduced E ∧
            (T : ℝ) * n₀ * D / C ≤ (Fintype.card V : ℝ) ∧
            (Fintype.card V : ℝ) ≤ C * ((T : ℝ) * n₀ * D) ∧
            (T : ℝ) * n₀ * ((P ^ t : ℕ) : ℝ) / C ≤ (numTR E : ℝ) ∧
            (numTR E : ℝ) ≤ C * ((T : ℝ) * n₀ * ((P ^ t : ℕ) : ℝ)) ∧
            (T : ℝ) * n₀ * ((P ^ t : ℕ) : ℝ) * (D : ℝ) ^ 2 / C ≤ (numTC E : ℝ) ∧
            (numTC E : ℝ) ≤ C * ((T : ℝ) * n₀ * ((P ^ t : ℕ) : ℝ) * (D : ℝ) ^ 2) ∧
            ∀ (A : Tester V) (q : ℝ), IsTwoSidedTester E ε A → A.QueriesAtMost q →
              c * (1 / Real.log (Fintype.card V : ℝ) *
                (Real.sqrt ((numTR E : ℝ) * (numTC E : ℝ)) / (ε * (Fintype.card V : ℝ)))) ≤ q := by sorry

end MonoTestDAG
