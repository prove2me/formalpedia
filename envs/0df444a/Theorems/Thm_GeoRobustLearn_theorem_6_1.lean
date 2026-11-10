-- Prove2me | Theorems.Thm_GeoRobustLearn_theorem_6_1
-- name    : GeoRobustLearn.theorem_6_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T04:08:54.87422+00:00
-- url     : https://prove2.me/theorems/58cddd12-7d16-4dd9-b71c-c1da8c528bd7
-- title:
--   Theorem 6.1 — learning $\mathcal C_K$: error $\mathrm{opt}_K+O(\varepsilon)$, $\mathrm{Bdry}_r(h)\le O(Kr)$, time $(d+1)^{\tilde O(K^2/\varepsilon^2+K^4r^2/\varepsilon^4)}$
-- statement:
--   There are an arithmetic-only training program, a deterministic arithmetic-only evaluation program and a constant $C$ such that the following holds. Let $d\ge1$, $K\ge1$, $0<r\le1/K$, $\varepsilon,\delta\in(0,1/4)$, and let $D$ be a distribution on $\mathbb R^d\times\{0,1\}$ whose first marginal is $\gamma$. Write
--
--   $$\mathrm{opt}_K=\inf_{f\in\mathcal C_K}\Pr_{(x,y)\sim D}[f(x)\ne y],\qquad R=(d+1)^{C(K^2/\varepsilon^2+K^4r^2/\varepsilon^4)(\log(2+K/\varepsilon+1/(Kr)))^C}(\log(2/\delta))^C.$$
--
--   Then:
--
--   1. on every sample stream, training halts within $R$ exact real-arithmetic operations, uses at most $R$ samples and returns a representation of at most $R$ reals, and the evaluation program computes the returned hypothesis $h$ at every point of $\mathbb R^d$ within $R$ operations;
--   2. $h$ takes values in $\{0,1\}$;
--   3. with probability at least $1-\delta$,
--   $$\Pr_{(x,y)\sim D}[h(x)\ne y]\le\mathrm{opt}_K+C\varepsilon\qquad\text{and}\qquad\mathrm{Bdry}_r(h)\le CKr.$$
--
--   The learner's own output is thus adversarially robust, at essentially the running time of non-robust agnostic learning of $\mathcal C_K$.
--
--   Differences from the source:
--   - reading: "Algorithm 2 returns a function h : ℝ^d → {0, 1}" → ∃ a training program P and a deterministic evaluation program E, chosen before d, K, r, ε, δ, D; h is E run on P's output, within the same budget on every query (FormulaBudget); reason: Theorem 1.2 says "There is an algorithm"; without a bounded evaluator the time bound would be vacuous (paper.md decision 2)
--   - reading: "running time, measured in exact real-arithmetic operations" → the published real RAM GeoLipLearn.Agnostic.Machine with both programs ArithmeticOnly and rational literals; bounds hold on every stream; reason: √, exp, log, Φ⁻¹ or Gaussian draws as unit-cost primitives would weaken the theorem (paper.md decision 4)
--   - encoding: O(ε), O(Kr), (d + 1)^{O(k)} poly(log 1/δ), k = Õ(K²/ε² + K⁴r²/ε⁴) → one natural C > 0 before all data: error ≤ opt_K + Cε, Bdry_r(h) ≤ CKr, budget robustBound C d K r ε δ; reason: the meaning of O/Õ with log factors depending on K, 1/ε, 1/(Kr) (paper.md decision 3)
--   - reading: ε, δ (Algorithm 2's Require) → ε, δ ∈ (0, 1/4); reason: the theorem names Algorithm 2, whose Require line fixes these ranges
--   - reading: d (dimension, unconstrained in the statement) → 1 ≤ d; reason: standing assumption of §5.1 (p.22); Theorem 6.1 is false at d = 0 (paper.md decision 6)
--   - encoding: D a distribution on ℝ^d × {0, 1} whose first marginal is γ → a probability measure on Space d × ℝ with GaussianInput D and labels in {0, 1} D-a.s. (BinaryLabels); reason: Lean representation; same instances
--   - encoding: Pr_{(x,y)∼D}[h(x) ≠ y], Bdry_r(h), opt_K → outer measures of the sets, with no measurability assumed of h or of members of C_K; reason: for measurable sets the same value; the bound on outer measures is the stronger statement (paper.md decision 8)
--   - reading: "with probability at least 1 − δ" → a measurable event of mass ≥ 1 − δ under the stream law (HighProbability), and both guarantees on that one event; reason: the published success-event convention; a stronger conclusion
-- source:
--   Lange, Marcussen, Vasilyan, Geometrically Constrained Learning I: Agnostically Learning Adversarially Robust Classifiers, manuscript (Nov. 3, 2026; sha256 8cbf3f52…), Theorem 6.1, pp.30–31 (PDF pp.30–31); Algorithm 2, p.31

import Definitions.Def_GeoLipLearn_Agnostic_Learner
import Definitions.Def_GeoRobustLearn_ArithmeticOnly
import Definitions.Def_GeoRobustLearn_BoundaryVolume

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace GeoRobustLearn

open GeoLipLearn.Agnostic

/-- **Theorem 6.1** (Learning a Boolean function), pp.30–31.

Lange, Marcussen, Vasilyan, *Geometrically Constrained Learning I: Agnostically Learning Adversarially
Robust Classifiers*, manuscript of November 3, 2026 (sha256 8cbf3f52…).

There are one arithmetic-only training program `P`, one deterministic arithmetic-only evaluation
program `E` and one constant `C`, chosen before all data, such that for every `d ≥ 1`, `K ≥ 1`,
`0 < r ≤ 1/K`, `ε, δ ∈ (0, 1/4)` and every distribution `D` on `ℝ^d × {0, 1}` with first marginal `γ`:
on every stream, training halts within `R = robustBound C d K r ε δ` steps with at most `R` samples
and a representation of at most `R` reals, and `E` evaluates the returned hypothesis `h` at every
query within `R` steps, with values in `{0, 1}`; and on a measurable event of probability at least
`1 − δ`, `Pr_D[h(x) ≠ y] ≤ opt_K + Cε` and `Bdry_r(h) ≤ CKr`.

**Formalization Note.** "Algorithm 2 returns h" is read as the existence of the programs, and
"returns a function" as a finite representation evaluated by `E` within the same budget
(`FormulaBudget`). `O(ε)`, `O(Kr)`, `(d+1)^{O(k)}`, `Õ(·)` and `poly(log 1/δ)` are pinned by the one
constant `C` as in `robustBound`. Probabilities of sets that may fail to be measurable are outer
measures; no measurability is assumed of `h` or of members of `C_K`. The inputs `[K, r, ε, δ]` are
the first four memory cells. `d ≥ 1` is the standing assumption of §5.1 (the theorem is false at
`d = 0`). -/
theorem theorem_6_1 :
    ∃ (P E : Program) (C : ℕ),
      Admissible P ∧ Admissible E ∧ ArithmeticOnly P ∧ ArithmeticOnly E ∧ Deterministic E ∧
      0 < C ∧
      ∀ (d : ℕ) (K r ε δ : ℝ) (D : Measure (Space d × ℝ)),
        1 ≤ d → IsProbabilityMeasure D → GaussianInput D → BinaryLabels D →
        1 ≤ K → 0 < r → r ≤ 1 / K → 0 < ε → ε < 1 / 4 → 0 < δ → δ < 1 / 4 →
        let R := robustBound C d K r ε δ
        let h : Streams d → Space d → ℝ := fun ω =>
          hypothesis (d := d) E R (representation (train P d 0 [K, r, ε, δ] R ω))
        FormulaBudget E d 0 [K, r, ε, δ] P R ∧
        (∀ ω x, h ω x = 0 ∨ h ω x = 1) ∧
        HighProbability (streamLaw D) δ (fun ω =>
          D {z | h ω z.1 ≠ z.2} ≤ optK K D + ENNReal.ofReal (C * ε) ∧
          bdry r (h ω) ≤ ENNReal.ofReal (C * K * r)) := by sorry

end GeoRobustLearn
