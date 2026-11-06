-- Prove2me | Theorems.Thm_LawLocalComp_lemma_2_1
-- name    : LawLocalComp.lemma_2_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T03:10:57.301548+00:00
-- url     : https://prove2.me/theorems/158dac18-e230-4c08-bf16-0b07c3383199
-- title:
--   Lemma 2.1 (Curvature and rank budgets)
-- statement:
--   Throughout, all vectors are nonnegative and $g$ is a norm monotone on $\mathbb R^d_+$.
--
--   1. For $z,a\in\mathbb R^d_+$ and $\phi(x)=g(z+xa)$ on $x\ge0$, there is a finite measure $\nu$ on $(0,\infty)$ such that for all $x\ge0$
--   $$\phi(x)=\phi(0)+\phi'_+(0)\,x+\int_0^\infty(x-t)_+\,\nu(dt),\qquad \int\nu(dt)\le g(a),\qquad\int t\,\nu(dt)\le g(z).\tag{4}$$
--   2. If nonnegative directions $a_1,\dots,a_n$ span at most $q$ dimensions and $\mu_j\ge0$, then
--   $$\sum_j\mu_j\,g(a_j)\le q\,g\Big(\sum_j\mu_ja_j\Big).\tag{5}$$
--
--   The hinge representation (4) and the rank budget (5) are the two budgets behind every norm transfer in the paper (Lemmas 2.3 and 2.4).
--
--   **Formalization Note** $\phi'_+(0)$ is the derivative within $[0,\infty)$ at $0$. Integrability of $t\mapsto t$ under $\nu$ is part of the conclusion.
--
--   Differences from the source:
--   - encoding: ∫_0^∞ against a nonnegative curvature measure ν → a finite measure ν on ℝ with ν((−∞, 0]) = 0 and t ↦ t integrable; reason: the right derivative φ'₊(0) already carries any mass at 0; integrability makes ∫ t dν a genuine integral
-- source:
--   Mahboub–Rahgoshay, Optimal Law-Local Compression for Stochastic Loads, STOC 2027 submission (manuscript of Oct. 29, 2026, sha256 5f71501c…aa873), Lemma 2.1, (4)–(5), p.3, with the standing hypotheses of §2, p.3

import Mathlib
import Definitions.Def_LawLocalComp_IsMonotoneNorm
import Definitions.Def_LawLocalComp_dirRank

namespace LawLocalComp

/-- **Lemma 2.1 (Curvature and rank budgets).**
Mahboub–Rahgoshay, *Optimal Law-Local Compression for Stochastic Loads*, STOC 2027
submission manuscript of Oct. 29, 2026 (sha256 5f71501c…aa873), Lemma 2.1, (4)–(5), p.3, under the standing hypotheses of §2, p.3 ("All vectors in this
section are nonnegative, and g is any norm monotone on the nonnegative orthant").

(4) For `z, a ≥ 0` and `ϕ(x) = g(z + xa)`, there is a finite measure `ν` on `(0, ∞)` with
`ν(ℝ) ≤ g(a)`, `∫ t dν ≤ g(z)` and `ϕ(x) = ϕ(0) + ϕ'₊(0) x + ∫ (x − t)₊ ν(dt)` for `x ≥ 0`.
(5) If nonnegative directions `a_j` span at most `q` dimensions and `µ_j ≥ 0`, then
`∑_j µ_j g(a_j) ≤ q g(∑_j µ_j a_j)`.

**Formalization Note.** `ϕ'₊(0)` is `derivWithin ϕ (Ici 0) 0`. `∫_0^∞` is read on `(0, ∞)`
(`ν(Iic 0) = 0`), which is forced by the right derivative. Integrability of `t` is stated so that
`∫ t dν` is not a junk value. -/
theorem lemma_2_1 {d : ℕ} (g : (Fin d → ℝ) → ℝ) (hg : IsMonotoneNorm g) :
    (∀ z a : Fin d → ℝ, 0 ≤ z → 0 ≤ a →
      ∃ ν : MeasureTheory.Measure ℝ, MeasureTheory.IsFiniteMeasure ν ∧ ν (Set.Iic 0) = 0 ∧
        ν Set.univ ≤ ENNReal.ofReal (g a) ∧ MeasureTheory.Integrable (fun t : ℝ => t) ν ∧
        ∫ t, t ∂ν ≤ g z ∧
        ∀ x : ℝ, 0 ≤ x → g (z + x • a) =
          g z + derivWithin (fun y : ℝ => g (z + y • a)) (Set.Ici 0) 0 * x + ∫ t, max (x - t) 0 ∂ν) ∧
    ∀ (n q : ℕ) (a : Fin n → Fin d → ℝ) (μ : Fin n → ℝ), (∀ j, 0 ≤ a j) → (∀ j, 0 ≤ μ j) →
      dirRank a ≤ q → ∑ j, μ j * g (a j) ≤ q * g (∑ j, μ j • a j) := by sorry

end LawLocalComp
