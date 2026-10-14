-- Prove2me | Theorems.Thm_OTSensitivity_Consist_theorem_21_2
-- name    : OTSensitivity.Consist.theorem_21_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T22:35:31.924522+00:00
-- url     : https://prove2.me/theorems/12ac83a6-ca82-455d-98db-ddc4e741d1e6
-- title:
--   Theorem 21 (2), (79), p. 39 — $\lim_M\lim_N\xi^K(Y^N,X^N\mid\mathcal F^M)=\xi^K(Y,X\mid\mathcal F)$
-- statement:
--   Let $\mathsf X$ and $\mathsf Y$ be Polish spaces. Let $k:\mathsf Y\times\mathsf Y\to[0,+\infty]$ be continuous with $k(y,y')=0\iff y=y'$, and let $a_1,a_2:\mathsf Y\to[0,\infty)$ be continuous with $k(y,y')\le a_1(y)+a_2(y')$. Let $\pi^N$ and $\pi$ be probability measures on $\mathsf X\times\mathsf Y$ (the joint laws of $(X^N,Y^N)$ and $(X,Y)$), with first marginal $\mu$ of $\pi$ and second marginals $\nu^N,\nu$, such that $\pi^N\to\pi$ weakly and (73) holds:
--   $$\lim_{N\to\infty}\int a\,d\nu^N=\int a\,d\nu<\infty,\qquad a=a_1+a_2.$$
--   Let $\mathscr X^M=\{X^M_h\}_{h=1}^{H(M)}$, $M\in\mathbb N$, be finite measurable partitions of $\mathsf X$ satisfying (75): $\mathcal F^M=\sigma(\mathscr X^M)\subseteq\mathcal F^{M+1}$ and $\mu(\partial X^M_h)=0$ for all $M,h$; let $\mathcal F=\bigvee_M\mathcal F^M$. Then the iterated limit exists and
--   $$\lim_{M\to\infty}\lim_{N\to\infty}\xi^K(Y^N,X^N\mid\mathcal F^M)=\xi^K(Y,X\mid\mathcal F),$$
--   for every choice of versions of the conditional distributions: for each $M$ the inner limit $L_M=\lim_N\xi^K(Y^N,X^N\mid\mathcal F^M)$ exists, and $L_M\to\xi^K(Y,X\mid\mathcal F)$.
--
--   This is the consistency of the partition estimator of the OT-based sensitivity measure: refining the partition after letting the sample size grow recovers the sensitivity measure of the generated $\sigma$-algebra.
--
--   **Formalization Note** $\mathsf X$, $\mathsf Y$ are Polish (the paper's supports in $\mathbb R^{n_X}$, $\mathbb R^{n_Y}$ are such spaces). Since $\xi^K$ depends on $(X,Y)$ only through the joint law, the statement is made on $\Omega=\mathsf X\times\mathsf Y$ with $\mathbb P=\pi^N$ (resp. $\pi$) and the coordinate projections, as the paper does in (81); weak convergence is Mathlib's topology on probability measures. Values are in $[0,+\infty]$; $K$ is `RWPI.SqrtLasso.transportCost`; conditional laws are arbitrary kernels satisfying the characterizing predicate. The iterated limit is stated as the existence of the inner limits $L_M$ and the convergence of $L_M$, with no junk-valued `lim`. The page prints $\xi^K(X,Y\mid\mathcal F)$ in (79); the paper's convention and the proof compute $\xi^K(Y,X\mid\mathcal F)$, which is what is stated. The paper assumes (73) "when k is not bounded"; it is assumed unconditionally, which loses nothing since a bounded $k$ satisfies it with constant $a_1=a_2$.
-- source:
--   Borgonovo, Figalli, Plischke & Savaré, Global Sensitivity Analysis via Optimal Transport, authors' manuscript of 7 March 2024 (Management Science, doi:10.1287/mnsc.2023.01796), Theorem 21 (2), (79), p. 39; setting (73), (75), (77), pp. 38–39; bounded separate costs, p. 4; §3.1, p. 9

import Mathlib
import Definitions.Def_RWPI_SqrtLasso_transportCost
import Definitions.Def_OTSensitivity_Consist_Setting
import Definitions.Def_OTSensitivity_Consist_Estimation

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace OTSensitivity.Consist

/-- Theorem 21 (2), (79), p. 39 (Borgonovo, Figalli, Plischke & Savaré, authors' manuscript of
7 March 2024). Let the joint laws `π^N` of `(X^N, Y^N)` converge weakly to the law `π` of `(X, Y)`
on `𝒳 × 𝒴`, let `k` be a continuous cost vanishing exactly on the diagonal with
`k(y, y') ≤ a₁(y) + a₂(y')`, and assume (73). If `𝒳^M = {X^M_h}` is a sequence of finite
measurable partitions satisfying (75) for `𝓕`, then the iterated limit
`lim_M lim_N ξ^K(Y^N, X^N | 𝓕^M)` exists and equals `ξ^K(Y, X | 𝓕)`, for every choice of versions
of the conditional distributions. (The page prints `ξ^K(X, Y | 𝓕)`; the paper's convention and
the proof compute `ξ^K(Y, X | 𝓕)`.) -/
theorem theorem_21_2 {𝒳 𝒴 : Type*}
    [TopologicalSpace 𝒳] [PolishSpace 𝒳] [MeasurableSpace 𝒳] [BorelSpace 𝒳]
    [TopologicalSpace 𝒴] [PolishSpace 𝒴] [MeasurableSpace 𝒴] [BorelSpace 𝒴]
    (k : 𝒴 → 𝒴 → ℝ≥0∞) (hk : IsCost k)
    (a₁ a₂ : 𝒴 → ℝ≥0) (ha : IsSeparateCostBound k a₁ a₂)
    (πs : ℕ → ProbabilityMeasure (𝒳 × 𝒴)) (π : ProbabilityMeasure (𝒳 × 𝒴))
    (hπ : Tendsto πs atTop (𝓝 π))
    (h73 : MomentConvergence a₁ a₂ (fun N => (πs N : Measure (𝒳 × 𝒴))) (π : Measure (𝒳 × 𝒴)))
    (H : ℕ → ℕ) (C : (M : ℕ) → Fin (H M) → Set 𝒳)
    (hC : IsPartitionSeq (π : Measure (𝒳 × 𝒴)).fst H C)
    (κs : ℕ → ℕ → Kernel 𝒳 𝒴)
    (hκs : ∀ M N, IsCondDistrib (πs N : Measure (𝒳 × 𝒴)) Prod.fst Prod.snd (cellSigma (C M))
      (κs M N))
    (κ : Kernel 𝒳 𝒴)
    (hκ : IsCondDistrib (π : Measure (𝒳 × 𝒴)) Prod.fst Prod.snd (⨆ M, cellSigma (C M)) κ) :
    ∃ L : ℕ → ℝ≥0∞,
      (∀ M, Tendsto (fun N => xi k (πs N : Measure (𝒳 × 𝒴)) Prod.fst Prod.snd (κs M N)) atTop
        (𝓝 (L M))) ∧
      Tendsto L atTop (𝓝 (xi k (π : Measure (𝒳 × 𝒴)) Prod.fst Prod.snd κ)) := by sorry

end OTSensitivity.Consist
