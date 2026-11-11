-- Prove2me | Theorems.Thm_IterRoundKMedian_Main_lemma_2_2
-- name    : IterRoundKMedian.Main.lemma_2_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T21:26:55.546197+00:00
-- url     : https://prove2.me/theorems/49dd7656-a0e6-4a26-8d72-422794571bd0
-- title:
--   Lemma 2.2 — weighted pipage concentration: Var(Z) ≤ v and Bernstein tails exp(−t²/(2(v + Mt/3)))
-- statement:
--   Let $y\in\mathbb R_{\ge0}^U$, $\delta>0$, and let $\hat y_i=\delta(\lfloor y_i/\delta\rfloor+X_i)$ where the rounded bits $X$ follow a pipage law for $(y,\delta)$. Let $a_i\ge0$ be deterministic weights and put
--   $$Z=\sum_i a_i\hat y_i,\qquad v=\delta\sum_i a_i^2y_i,\qquad M=\delta\max_i a_i.$$
--   Then $\mathrm{Var}(Z)\le v$; for every $t>0$,
--   $$\Pr[Z\le\mathbb EZ-t]\le\exp\Big(-\frac{t^2}{2(v+Mt/3)}\Big),\qquad \Pr[Z\ge\mathbb EZ+t]\le\exp\Big(-\frac{t^2}{2(v+Mt/3)}\Big);$$
--   and if $v=0$ then $Z$ is deterministic and both probabilities vanish.
--
--   This Bernstein-type inequality replaces the independent-variable Bernstein inequality for the dependent pipage rounding; the preprocessing of §3 uses it to control the rounded totals.
--
--   Differences from the source:
--
--   - generalization: ŷ is the output of the pipage rounding procedure of §2 (for a laminar family) → the rounded bits follow any law with E[X_i] = f_i and the three inequalities (7) for every S ⊆ U (IsPipageLaw); reason: the procedure's output law has these properties (p. 12), so the statement specializes to the source
--   - encoding: probabilities and expectations of the rounding → a finite law on {0,1}^U (FinLaw) with finite sums; reason: the procedure has finitely many outcomes
--   - encoding: M = δ max_i a_i → δ * ⨆ i, a i; reason: a ≥ 0 on a finite index set; equals the maximum (0 for empty U)
--   - encoding: Z is deterministic → every outcome of positive probability has Z = E Z; reason: same meaning for a finite law
-- source:
--   Byrka, Guo, Hu, Li, Shin, Vajanopath, Wan, Wang, Iterative Randomized Rounding for k-Median in General and Euclidean Metrics, STOC 2027 submission (manuscript sha256 02f6267b…), p. 12, Lemma 2.2

import Mathlib
import Definitions.Def_IterRoundKMedian_Main_PipageLaw

namespace IterRoundKMedian.Main

theorem lemma_2_2 {U : Type*} [Fintype U] [DecidableEq U]
    (y : U → ℝ) (hy : ∀ i, 0 ≤ y i) (δ : ℝ) (hδ : 0 < δ)
    (μ : FinLaw (U → Bool)) (hμ : IsPipageLaw y δ μ)
    (a : U → ℝ) (ha : ∀ i, 0 ≤ a i) :
    let Z : (U → Bool) → ℝ := fun X => ∑ i, a i * pipageOutput y δ X i
    let v : ℝ := δ * ∑ i, a i ^ 2 * y i
    let M : ℝ := δ * ⨆ i, a i
    μ.var Z ≤ v ∧
      (∀ t : ℝ, 0 < t →
        μ.pr (fun X => Z X ≤ μ.expect Z - t) ≤ Real.exp (-(t ^ 2 / (2 * (v + M * t / 3)))) ∧
        μ.pr (fun X => μ.expect Z + t ≤ Z X) ≤ Real.exp (-(t ^ 2 / (2 * (v + M * t / 3))))) ∧
      (v = 0 →
        (∀ X, μ.prob X ≠ 0 → Z X = μ.expect Z) ∧
        ∀ t : ℝ, 0 < t →
          μ.pr (fun X => Z X ≤ μ.expect Z - t) = 0 ∧
          μ.pr (fun X => μ.expect Z + t ≤ Z X) = 0) := by sorry

end IterRoundKMedian.Main
