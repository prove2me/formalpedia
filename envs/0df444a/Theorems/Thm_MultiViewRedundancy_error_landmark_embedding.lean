-- Prove2me | Theorems.Thm_MultiViewRedundancy_error_landmark_embedding
-- name    : MultiViewRedundancy.error_landmark_embedding
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-23T19:22:15.471637+00:00
-- url     : https://prove2.me/theorems/ba53c009-6884-425c-a25a-142ef44b1000
-- title:
--   Theorem 10 (as proved): risk of the landmark embedding of an approximate solution
-- statement:
--   Assume $|Y|\le1$ almost surely, $Z$ valued in a standard Borel space and $p_{X,Z}\ll p_X\otimes p_Z$. Let $G$ be a common upper bound, $p_X\otimes p_Z$-almost everywhere, of $g^\star$ and of $g:=\exp\circ f$ for a measurable $f:\mathcal X\times\mathcal Z\to\mathbb R$ with finite $L_{\mathrm{lm}}(f)$. Let $\varepsilon_{\mathrm{opt,lm}}=L_{\mathrm{lm}}(f)-L_{\mathrm{lm}}(\log\circ g^\star)$ and $\varphi(x)=(g(x,Z_1),\dots,g(x,Z_m))$ with $Z_1,\dots,Z_m$ i.i.d. copies of $Z$. Let $0<\delta<1$, $n=\lfloor m/\lceil\log_2(1/\delta)\rceil\rfloor$, $m\ge\lceil\log_2(1/\delta)\rceil$ and $\varepsilon_{\mathrm{lm}}=2\operatorname{var}(\mathbb E[Y_1\mid Z_1]g^\star(X,Z_1))/n$. With probability at least $1-\delta$,
--
--   $$R(\varphi)\le2\varepsilon_{\mathrm{lm}}+4(1+G)^2\sqrt{2\varepsilon_{\mathrm{opt,lm}}\varepsilon_{\mathrm{lm}}}+16(1+G)^4\varepsilon_{\mathrm{opt,lm}}.$$
--
--   The downstream risk of the landmark embedding of an imperfect contrastive solution degrades smoothly with its excess contrastive loss.
--
--   **Formalization Note** The paper uses the block size $\lfloor m/\log_2(1/\delta)\rfloor$. Its proof splits the $m$ landmarks into $\lfloor m/n\rfloor$ disjoint blocks and needs at least $\log_2(1/\delta)$ of them. That number can be smaller, for example $m=3$ and $\log_2(1/\delta)=1.5$ give one block, so the statement is the one the proof establishes, with block size $n=\lfloor m/\lceil\log_2(1/\delta)\rceil\rfloor$. The two coincide when $\log_2(1/\delta)$ is an integer. "With probability at least $1-\delta$" is written as: the set of landmark tuples for which the conclusion fails has (outer) probability at most $\delta$. The paper's $g_{\max}=\sup_{\operatorname{supp}p_X\otimes p_Z}g^\star$ is replaced by any almost-everywhere upper bound $G$ of $g^\star$ and $g$, which is all the proof uses; $G=g_{\max}$ is a special case. Finiteness of $L_{\mathrm{lm}}(f)$ is a hypothesis (otherwise the bound is infinite). $L_{\mathrm{lm}}(\log\circ g^\star)$ is written in the equal form $L_{\mathrm{direct}}(g^\star)$. The paper's $f:\mathcal X\times\mathcal X\to\mathbb R$ is a typo for $\mathcal X\times\mathcal Z$.
-- source:
--   Tosh, Krishnamurthy and Hsu, Contrastive learning, multi-view redundancy, and linear models, arXiv:2008.10150v2 (2021), Section 5, Theorem 10, p. 12; proof in Appendix A.9, pp. 22-23

import Mathlib
import Definitions.Def_MultiViewRedundancy_Basic

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace MultiViewRedundancy

theorem error_landmark_embedding {X Z : Type*} [MeasurableSpace X] [MeasurableSpace Z]
    [StandardBorelSpace Z] [Nonempty Z]
    (ρ : Measure (X × Z × ℝ)) [IsProbabilityMeasure ρ] (hY : ∀ᵐ t ∂ρ, |t.2.2| ≤ 1)
    (hac : lawXZ ρ ≪ (lawXZ ρ).fst.prod (lawXZ ρ).snd)
    (f : X → Z → ℝ) (hf : Measurable (Function.uncurry f)) (G : ℝ)
    (hGs : ∀ᵐ p ∂(lawXZ ρ).fst.prod (lawXZ ρ).snd, densityRatio (lawXZ ρ) p.1 p.2 ≤ G)
    (hGf : ∀ᵐ p ∂(lawXZ ρ).fst.prod (lawXZ ρ).snd, Real.exp (f p.1 p.2) ≤ G)
    (hint : Integrable (fun t => Real.log (1 + Real.exp (-(t.2.2 * f t.1 t.2.1))))
      (contrastDist (lawXZ ρ)))
    (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) (m : ℕ) (hm : ⌈Real.logb 2 (1 / δ)⌉₊ ≤ m) :
    Measure.pi (fun _ : Fin m => (lawXZ ρ).snd)
      {zs | ¬ risk ρ (landmarkEmbedding (fun x z => Real.exp (f x z)) zs) ≤
          ENNReal.ofReal (2 * epsLm ρ ⌊(m : ℝ) / ⌈Real.logb 2 (1 / δ)⌉₊⌋₊ +
            4 * (1 + G) ^ 2 * Real.sqrt (2 * epsOptLm (lawXZ ρ) f *
              epsLm ρ ⌊(m : ℝ) / ⌈Real.logb 2 (1 / δ)⌉₊⌋₊) +
            16 * (1 + G) ^ 4 * epsOptLm (lawXZ ρ) f)} ≤ ENNReal.ofReal δ := by sorry

end MultiViewRedundancy
