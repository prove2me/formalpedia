-- Prove2me | Theorems.Thm_MultiViewRedundancy_landmark_embedding_error
-- name    : MultiViewRedundancy.landmark_embedding_error
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-23T19:19:37.381971+00:00
-- url     : https://prove2.me/theorems/e6a36771-59e0-4206-a6f8-c7fa12906683
-- title:
--   Theorem 3 (as proved): linear predictors on landmark embeddings are nearly optimal
-- statement:
--   Let $(X_1,Z_1,Y_1),\dots,(X_m,Z_m,Y_m),(X,Z,Y)$ be i.i.d. with $\mathbb E[Y^2]<\infty$, $Z$ valued in a standard Borel space and $p_{X,Z}\ll p_X\otimes p_Z$. Let $\varphi^\star(x)=(g^\star(x,Z_1),\dots,g^\star(x,Z_m))$ be the landmark embedding of the density ratio $g^\star=p_{X,Z}/(p_X\otimes p_Z)$. Let $0<\delta<1$, let $n=\lfloor m/\lceil\log_2(1/\delta)\rceil\rfloor$, and assume $m\ge\lceil\log_2(1/\delta)\rceil$. Let $\varepsilon_{\mathrm{lm}}=2\operatorname{var}(\mathbb E[Y_1\mid Z_1]\,g^\star(X,Z_1))/n$, assumed finite, and let $\varepsilon_\mu=\varepsilon_X+2\sqrt{\varepsilon_X\varepsilon_Z}+\varepsilon_Z$. Then with probability at least $1-\delta$ over $Z_1,\dots,Z_m$ there is $w\in\mathbb R^m$ with
--
--   $$\mathbb E\big[(w^\top\varphi^\star(X)-\mathbb E[Y\mid X,Z])^2\mid Z_1,\dots,Z_m\big]\le\varepsilon_\mu+2\sqrt{\varepsilon_\mu\varepsilon_{\mathrm{lm}}}+\varepsilon_{\mathrm{lm}}.$$
--
--   This is the paper's main result: a linear function of the landmark embedding built from the contrastive solution is nearly as good as the Bayes predictor $\mathbb E[Y\mid X,Z]$ when the views are redundant and there are many landmarks.
--
--   **Formalization Note** The paper uses the block size $\lfloor m/\log_2(1/\delta)\rfloor$. Its proof splits the $m$ landmarks into $\lfloor m/n\rfloor$ disjoint blocks and needs at least $\log_2(1/\delta)$ of them. That number can be smaller, for example $m=3$ and $\log_2(1/\delta)=1.5$ give one block, so the statement is the one the proof establishes, with block size $n=\lfloor m/\lceil\log_2(1/\delta)\rceil\rfloor$. The two coincide when $\log_2(1/\delta)$ is an integer. "With probability at least $1-\delta$" is written as: the set of landmark tuples for which the conclusion fails has (outer) probability at most $\delta$. The conditional expectation is the integral over a fresh $(X,Z,Y)\sim\rho$ at fixed landmarks.
-- source:
--   Tosh, Krishnamurthy and Hsu, Contrastive learning, multi-view redundancy, and linear models, arXiv:2008.10150v2 (2021), Section 3.1, Theorem 3, p. 8 (restated in Section 1.1, p. 3)

import Mathlib
import Definitions.Def_MultiViewRedundancy_Basic

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace MultiViewRedundancy

theorem landmark_embedding_error {X Z : Type*} [MeasurableSpace X] [MeasurableSpace Z]
    [StandardBorelSpace Z] [Nonempty Z]
    (ρ : Measure (X × Z × ℝ)) [IsProbabilityMeasure ρ] (hY : MemLp (fun t => t.2.2) 2 ρ)
    (hac : lawXZ ρ ≪ (lawXZ ρ).fst.prod (lawXZ ρ).snd) (hV : landmarkVar ρ ≠ ⊤)
    (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) (m : ℕ) (hm : ⌈Real.logb 2 (1 / δ)⌉₊ ≤ m) :
    Measure.pi (fun _ : Fin m => (lawXZ ρ).snd)
      {zs | ¬ ∃ w : Fin m → ℝ,
        ∫⁻ t, ENNReal.ofReal
            ((∑ i, w i * landmarkEmbedding (densityRatio (lawXZ ρ)) zs t.1 i -
              regXZ ρ t.1 t.2.1) ^ 2) ∂ρ ≤
          ENNReal.ofReal (epsMu ρ +
            2 * Real.sqrt (epsMu ρ * epsLm ρ ⌊(m : ℝ) / ⌈Real.logb 2 (1 / δ)⌉₊⌋₊) +
            epsLm ρ ⌊(m : ℝ) / ⌈Real.logb 2 (1 / δ)⌉₊⌋₊)} ≤ ENNReal.ofReal δ := by sorry

end MultiViewRedundancy
