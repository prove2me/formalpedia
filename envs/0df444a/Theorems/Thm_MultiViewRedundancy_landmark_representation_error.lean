-- Prove2me | Theorems.Thm_MultiViewRedundancy_landmark_representation_error
-- name    : MultiViewRedundancy.landmark_representation_error
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-23T19:19:05.044836+00:00
-- url     : https://prove2.me/theorems/b3abc91e-4026-4824-ac2e-559e3903fbad
-- title:
--   Lemma 2 (as proved): landmark embedding error
-- statement:
--   Let $(X_1,Z_1,Y_1),\dots,(X_m,Z_m,Y_m),(X,Z,Y)$ be i.i.d. with $\mathbb E[Y^2]<\infty$, $Z$ valued in a standard Borel space and $p_{X,Z}\ll p_X\otimes p_Z$. Let $\varphi^\star(x)=(g^\star(x,Z_1),\dots,g^\star(x,Z_m))$. Let $0<\delta<1$, let $n=\lfloor m/\lceil\log_2(1/\delta)\rceil\rfloor$, and assume $m\ge\lceil\log_2(1/\delta)\rceil$, so that $n\ge1$. Assume $V:=\operatorname{var}(\mathbb E[Y_1\mid Z_1]\,g^\star(X,Z_1))<\infty$, where $X$ and $Z_1$ are independent. Then with probability at least $1-\delta$ over $Z_1,\dots,Z_m$ there is $w\in\mathbb R^m$ with
--
--   $$\mathbb E\big[(w^\top\varphi^\star(X)-\mu(X))^2\mid Z_1,\dots,Z_m\big]\le\varepsilon_{\mathrm{lm}}:=\frac{2V}{n}.$$
--
--   **Formalization Note** The paper uses the block size $\lfloor m/\log_2(1/\delta)\rfloor$. Its proof splits the $m$ landmarks into $\lfloor m/n\rfloor$ disjoint blocks and needs at least $\log_2(1/\delta)$ of them. That number can be smaller, for example $m=3$ and $\log_2(1/\delta)=1.5$ give one block, so the statement is the one the proof establishes, with block size $n=\lfloor m/\lceil\log_2(1/\delta)\rceil\rfloor$. The two coincide when $\log_2(1/\delta)$ is an integer. "With probability at least $1-\delta$" is written as: the set of landmark tuples for which the conclusion fails has (outer) probability at most $\delta$. The conditional expectation given the landmarks is the integral over $X\sim p_X$ at fixed landmarks. Finiteness of $\mathbb E[Y^2]$ and of $V$ (otherwise the bound is infinite) and $p_{X,Z}\ll p_X\otimes p_Z$ (which holds whenever the densities of Section 2.1 exist) are hypotheses.
-- source:
--   Tosh, Krishnamurthy and Hsu, Contrastive learning, multi-view redundancy, and linear models, arXiv:2008.10150v2 (2021), Section 3.1, Lemma 2, p. 8; proof in Appendix A.2, pp. 16-17

import Mathlib
import Definitions.Def_MultiViewRedundancy_Basic

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace MultiViewRedundancy

theorem landmark_representation_error {X Z : Type*} [MeasurableSpace X] [MeasurableSpace Z]
    [StandardBorelSpace Z] [Nonempty Z]
    (ρ : Measure (X × Z × ℝ)) [IsProbabilityMeasure ρ] (hY : MemLp (fun t => t.2.2) 2 ρ)
    (hac : lawXZ ρ ≪ (lawXZ ρ).fst.prod (lawXZ ρ).snd) (hV : landmarkVar ρ ≠ ⊤)
    (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) (m : ℕ) (hm : ⌈Real.logb 2 (1 / δ)⌉₊ ≤ m) :
    Measure.pi (fun _ : Fin m => (lawXZ ρ).snd)
      {zs | ¬ ∃ w : Fin m → ℝ,
        ∫⁻ x, ENNReal.ofReal
            ((∑ i, w i * landmarkEmbedding (densityRatio (lawXZ ρ)) zs x i - muFn ρ x) ^ 2)
            ∂(lawXZ ρ).fst ≤
          ENNReal.ofReal (epsLm ρ ⌊(m : ℝ) / ⌈Real.logb 2 (1 / δ)⌉₊⌋₊)} ≤ ENNReal.ofReal δ := by sorry

end MultiViewRedundancy
