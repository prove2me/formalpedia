-- Prove2me | Theorems.Thm_MultiViewRedundancy_error_direct_embedding
-- name    : MultiViewRedundancy.error_direct_embedding
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-23T19:22:45.879751+00:00
-- url     : https://prove2.me/theorems/8c78ce31-b3f5-4241-91c5-66ddd2710a84
-- title:
--   Theorem 11: risk of direct embeddings and the excess contrastive loss
-- statement:
--   Let $(X,Z,Y)$ have $\mathbb E[Y^2]<\infty$, $Z$ valued in a standard Borel space and $p_{X,Z}\ll p_X\otimes p_Z$. Let $\eta:\mathcal X\to\mathbb R^m$ and $\psi:\mathcal Z\to\mathbb R^m$ be measurable with $0<\eta(x)^\top\psi(z)$ for $p_X\otimes p_Z$-almost every $(x,z)$ and with finite $L_{\mathrm{direct}}(\eta^\top\psi)$. Let $G$ be a common upper bound, $p_X\otimes p_Z$-almost everywhere, of $g^\star$ and $\eta^\top\psi$. Then
--
--   $$R(\eta)\le\mathbb E[Y^2]\,(1+G)^4\,\varepsilon_{\mathrm{opt,direct}},\qquad\varepsilon_{\mathrm{opt,direct}}=L_{\mathrm{direct}}\big((x,z)\mapsto\eta(x)^\top\psi(z)\big)-L_{\mathrm{direct}}(g^\star).$$
--
--   **Formalization Note** The paper's $g_{\max}$ is replaced by any almost-everywhere upper bound $G$ of $g^\star$ and $\eta^\top\psi$, which is all the proof uses. Positivity of $\eta^\top\psi$ is needed for $L_{\mathrm{direct}}$ (a logarithm of $1+1/(\eta^\top\psi)$) to be defined and for $\eta^\top\psi/(1+\eta^\top\psi)$ to be a probability in the proof's Pinsker step. Finiteness of $L_{\mathrm{direct}}(\eta^\top\psi)$ is a hypothesis (otherwise the bound is infinite). $R(\eta)$ takes values in $[0,\infty]$.
-- source:
--   Tosh, Krishnamurthy and Hsu, Contrastive learning, multi-view redundancy, and linear models, arXiv:2008.10150v2 (2021), Section 5, Theorem 11, p. 12; proof in Appendix A.10, p. 23

import Mathlib
import Definitions.Def_MultiViewRedundancy_Basic

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace MultiViewRedundancy

theorem error_direct_embedding {X Z : Type*} [MeasurableSpace X] [MeasurableSpace Z]
    [StandardBorelSpace Z] [Nonempty Z]
    (ρ : Measure (X × Z × ℝ)) [IsProbabilityMeasure ρ] (hY : MemLp (fun t => t.2.2) 2 ρ)
    (hac : lawXZ ρ ≪ (lawXZ ρ).fst.prod (lawXZ ρ).snd)
    {m : ℕ} (η : X → Fin m → ℝ) (ψ : Z → Fin m → ℝ) (hη : Measurable η) (hψ : Measurable ψ)
    (G : ℝ)
    (hGs : ∀ᵐ p ∂(lawXZ ρ).fst.prod (lawXZ ρ).snd, densityRatio (lawXZ ρ) p.1 p.2 ≤ G)
    (hGe : ∀ᵐ p ∂(lawXZ ρ).fst.prod (lawXZ ρ).snd, innerEmb η ψ p.1 p.2 ≤ G)
    (hpos : ∀ᵐ p ∂(lawXZ ρ).fst.prod (lawXZ ρ).snd, 0 < innerEmb η ψ p.1 p.2)
    (hint : Integrable (fun t => Real.log (1 + 1 / innerEmb η ψ t.1 t.2.1 ^ t.2.2))
      (contrastDist (lawXZ ρ))) :
    risk ρ η ≤
      ENNReal.ofReal ((∫ t, t.2.2 ^ 2 ∂ρ) * (1 + G) ^ 4 * epsOptDirect (lawXZ ρ) η ψ) := by sorry

end MultiViewRedundancy
