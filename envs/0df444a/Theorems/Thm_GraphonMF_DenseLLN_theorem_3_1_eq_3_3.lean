-- Prove2me | Theorems.Thm_GraphonMF_DenseLLN_theorem_3_1_eq_3_3
-- name    : GraphonMF.DenseLLN.theorem_3_1_eq_3_3
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-11-05T01:51:13.287541+00:00
-- url     : https://prove2.me/theorems/0fe4f569-937e-4678-93f5-158dd4e16393
-- title:
--   Theorem 3.1, (3.3), p. 3595 — μⁿ → μ̄ in 𝒫(𝒞_d) in probability
-- statement:
--   Let $I=[0,1]$, $T>0$, and let the initial states $X_u(0)\sim\mu_u(0)$ and the standard Brownian motions $B_u$, $u\in I$, be mutually independent on one probability space. Assume
--
--   1. Condition 2.1: $u\mapsto\mu_u(0)$ is measurable, $\sup_u\mathbb E|X_u(0)|^{2+\varepsilon}<\infty$ for some $\varepsilon>0$, and $b,\sigma$ are Lipschitz;
--   2. Condition 2.2(a): for a finite cover of $I$ by intervals $I_1,\dots,I_N$, $u\mapsto\mu_u(0)$ is $W_2$-continuous on each $I_i$;
--   3. Condition 3.1: each $G_n$ is a step graphon as in (3.2); the weights satisfy either $\xi^n_{ij}=G_n(i/n,j/n)$, or $\xi^n_{ij}=\xi^n_{ji}\sim\mathrm{Bernoulli}(G_n(i/n,j/n))$ independently for $i\le j$ and independently of the noise; and $\|G_n-G\|_\square\to0$ for a graphon $G$.
--
--   Let $X=(X_u)_{u\in I}$ solve the graphon particle system (2.1) for $G$, with path laws $\mu_u$, and let $X^n=(X^n_1,\dots,X^n_n)$ solve the $n$-particle system (3.1), driven by $X_{i/n}(0)$ and $B_{i/n}$. Then
--   $$\mu^n:=\frac1n\sum_{i=1}^n\delta_{X^n_i}\ \longrightarrow\ \bar\mu:=\int_I\mu_u\,du\quad\text{in }\mathcal P(\mathcal C_d)\text{ in probability}\tag{3.3}$$
--   as $n\to\infty$.
--
--   This is the first assertion of Theorem 3.1; it needs no regularity of $G$ (Condition 2.2(b) is not assumed). It is stated separately because the second assertion (3.4) follows directly from Lemma 6.1 and Remark 2.1, while (3.3) needs the continuous-graphon approximation of §6.2.
--
--   **Formalization Note** Same conventions as the parent theorem `GraphonMF.DenseLLN.theorem_3_1`: convergence in probability means that for every neighbourhood $U$ of $\bar\mu$ in the weak topology, $\mathbb P(\mu^n\notin U)\to0$ with $\mathbb P$ applied as an outer measure; $\bar\mu$ is the mixture $\int_I\mu_u\,du$; each $\xi^n$ is assumed measurable. The hypotheses are exactly those of the parent theorem.
-- source:
--   Bayraktar, Chakraborty, Wu, Graphon mean field systems, Ann. Appl. Probab. 33(5) (2023), p. 3595, Theorem 3.1, display (3.3); proof in §6.2, p. 3608

import Mathlib
import Definitions.Def_GraphonMF_DenseLLN_Setting

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace GraphonMF.DenseLLN
theorem theorem_3_1_eq_3_3 {Ω : Type*} [MeasurableSpace Ω] {T : ℝ≥0} {d N : ℕ} {P : Measure Ω}
    {μ0 : GraphonMF.Stability.I → Measure (GraphonMF.Stability.State d)} {X0 : GraphonMF.Stability.I → Ω → GraphonMF.Stability.State d} {B : GraphonMF.Stability.I → ℝ≥0 → Ω → GraphonMF.Stability.State d}
    (noise : NoiseSetting P μ0 X0 B) (hT : 0 < T)
    (b : GraphonMF.Stability.State d → GraphonMF.Stability.State d → GraphonMF.Stability.State d) (σ : GraphonMF.Stability.State d → GraphonMF.Stability.State d → Matrix (Fin d) (Fin d) ℝ)
    (ε : ℝ) (h21 : GraphonMF.Stability.Cond21 ε μ0 b σ)
    (J : Fin N → Set GraphonMF.Stability.I) (h22a : Cond22a μ0 J)
    (G : GraphonMF.Stability.I → GraphonMF.Stability.I → ℝ) (hG : GraphonMF.Stability.IsGraphon G)
    (Gs : ℕ → GraphonMF.Stability.I → GraphonMF.Stability.I → ℝ) (h31a : ∀ n, 0 < n → GraphonMF.Stability.IsStepGraphon n (Gs n))
    (ξ : (n : ℕ) → Ω → Fin n → Fin n → ℝ) (hξ : ∀ n, Measurable (ξ n))
    (h31b : Cond31b P X0 B ξ Gs)
    (h31c : Tendsto (fun n => GraphonMF.Stability.cutNorm (fun u v => Gs n u v - G u v)) atTop (𝓝 0))
    (X : GraphonMF.Stability.I → Ω → GraphonMF.Stability.Cd T d) (hX : IsGraphonSolution noise G b σ X)
    (Xn : (n : ℕ) → Fin n → Ω → GraphonMF.Stability.Cd T d)
    (hXn : ∀ n, IsParticleSolution noise b σ n (ξ n) (hξ n) (Xn n)) :
    TendstoInProb P (fun n ω => empiricalPM (fun i => Xn n i ω)) (mixturePM P X) := by sorry
end GraphonMF.DenseLLN
