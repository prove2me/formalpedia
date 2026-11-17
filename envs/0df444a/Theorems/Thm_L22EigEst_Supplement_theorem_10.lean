-- Prove2me | Theorems.Thm_L22EigEst_Supplement_theorem_10
-- name    : L22EigEst.Supplement.theorem_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T12:38:18.897297+00:00
-- url     : https://prove2.me/theorems/e066bab0-ac81-41f4-aa57-9d57c738af83
-- title:
--   Theorem 10 — spectral norm decay [RV07]: $\mathbb E\|AS^\intercal\|_2 \le \|A\|_2 + C_0(\mathbb E[\log(e+|S|)\,\|AS^\intercal\|_{1\to2}^2])^{1/2}$
-- statement:
--   **Theorem 10 (Spectral Norm Decay, after Rudelson–Vershynin).** There is a universal constant $C_0>0$ such that the following holds for all $d,n\in\mathbb N$, every real matrix $A\in\mathbb R^{d\times n}$ and all $p_1,\dots,p_n\in(0,1]$. Let $\delta_1,\dots,\delta_n$ be independent with $\delta_i\sim\mathrm{Ber}(p_i)$, let $S$ be the random $n\times n$ diagonal matrix with $S_{ii}=\delta_i/\sqrt{p_i}$, and let $|S|=\sum_i\delta_i$. Then
--
--   $$\mathbb E_S\big[\|AS^\intercal\|_2\big]\;\le\;\|A\|_2+C_0\Big(\mathbb E_S\big[\log(e+|S|)\cdot\|AS^\intercal\|_{1\to2}^2\big]\Big)^{1/2},$$
--
--   where $\|\cdot\|_2$ is the spectral (operator) norm and $\|AS^\intercal\|_{1\to2}$ is the maximum column norm of $AS^\intercal$.
--
--   The bound says that sampling columns with importance weights $1/\sqrt{p_i}$ cannot inflate the spectral norm by more than a term governed by the largest rescaled sampled column. Applied twice after decoupling, it is the main tool in the paper's proof of Lemma 4.10.
--
--   **Formalization Note** The expectation is the finite sum over sampling patterns $\delta\in\{0,1\}^n$ with product Bernoulli weights (`bernExp`); $S$ is the base mission's `sampMat p δ`, $|S|$ is `sampCount δ`, and $AS^\intercal$ is `A * sampMat p δ`. The spectral norm of the rectangular matrix is the published `WainwrightHDS.NucNorm.opNorm2`, which equals the base mission's square `opNorm2` when $d=n$.
--
--   Differences from the source:
--   - encoding: E_S over independent δ_i ∼ Ber(p_i); S the n × n diagonal matrix with S_ii = δ_i/√p_i; |S| = Σ_i δ_i; AS⊺ → bernExp p (finite sum over δ : Fin n → Bool with product Bernoulli weights); sampMat p δ; sampCount δ; A * sampMat p δ; reason: the base mission's published conventions; S is diagonal so S⊺ = S; same random variables
--   - encoding: p_i implicit (Ber(p_i) and the rescaling 1/√p_i) → ∀ i, 0 < p i ∧ p i ≤ 1; reason: the range in which Ber(p_i) and δ_i/√p_i are defined; it excludes only undefined cases
--   - encoding: a universal constant C0 → ∃ C₀ > 0 chosen before d, n, A and p; reason: the square-root term is nonnegative, so any working constant can be enlarged to a positive one; equivalent
--   - encoding: (E_S[…])^{1/2}, ∥·∥2, ∥·∥1→2, log, e → Real.sqrt of the (nonnegative) expectation; the operator norm EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin d) (WainwrightHDS.NucNorm.opNorm2); colNormRect; Real.log; Real.exp 1; reason: Lean conventions; same values
-- source:
--   Menand, Waingarten, Dimension-Free ℓ₂²-Sampling Algorithms for Eigenvalue Estimation, STOC 2027 submission (manuscript sha256 b1f6adce…), Theorem 10, p.36 (proof Appendix A.2, pp.37–38)

import Definitions.Def_L22EigEst_bernW
import Definitions.Def_L22EigEst_sampMat
import Definitions.Def_WainwrightHDS_NucNorm_opNorm2
import Definitions.Def_L22EigEst_Supplement_colNormRect

open WainwrightHDS.NucNorm

namespace L22EigEst.Supplement

/-- **Theorem 10 (Spectral Norm Decay [RV07])** (p.36, proved in Appendix A.2, pp.37–38), Menand,
Waingarten, *Dimension-Free ℓ₂²-Sampling Algorithms for Eigenvalue Estimation*, STOC 2027 submission
(manuscript sha256 b1f6adce…): "Let A ∈ ℝ^{d×n}, and let S be a random n × n diagonal matrix with
S_ii = δ_i/√p_i, where the δ_i ∼ Ber(p_i) are independent, and let |S| = Σ_i δ_i. Then, for a
universal constant C0, E_S[∥AS⊺∥2] ≤ ∥A∥2 + C0 (E_S[log(e + |S|) · ∥AS⊺∥²_{1→2}])^{1/2}, where
∥AS⊺∥1→2 is the maximum column norm of AS⊺."

**Formalization Note.**
* `S = sampMat p δ` (diagonal, so `S⊺ = S` and `AS⊺ = A * sampMat p δ`), `|S| = sampCount δ`;
  `E_S` is the finite sum `bernExp p` with independent Bernoulli product weights.
* `p_i ∈ (0, 1]`, implicit in `Ber(p_i)` and the rescaling `1/√p_i`.
* `∥·∥2` is the ℓ₂ operator norm of a rectangular matrix (`WainwrightHDS.NucNorm.opNorm2`), and
  `∥·∥1→2` the maximum column norm (`colNormRect`); `log` is natural, `e = exp 1`.
* `C₀` is one universal constant, chosen before `d`, `n`, `A` and `p`; `0 < C₀` is harmless, as the
  square-root term is nonnegative. -/
theorem theorem_10 :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ (d n : ℕ) (A : Matrix (Fin d) (Fin n) ℝ) (p : Fin n → ℝ),
      (∀ i, 0 < p i ∧ p i ≤ 1) →
      L22EigEst.bernExp p (fun δ => opNorm2 (A * L22EigEst.sampMat p δ)) ≤
        opNorm2 A + C₀ * Real.sqrt (L22EigEst.bernExp p (fun δ =>
          Real.log (Real.exp 1 + (L22EigEst.sampCount δ : ℝ)) *
            colNormRect (A * L22EigEst.sampMat p δ) ^ 2)) := by sorry

end L22EigEst.Supplement
