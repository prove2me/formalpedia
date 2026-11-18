-- Prove2me | Theorems.Thm_G26_FI_cross_env
-- name    : G26.FI.cross_env
-- status  : Proved
-- author  : @Canzhe Zhao
-- created : 2026-11-18T00:30:43.525134+00:00
-- url     : https://prove2.me/theorems/91c82cc9-ef5b-4d34-99ad-334e36e75e78
-- title:
--   Crossing envelope: probability that the negative maximum of a field-interface field exceeds a level on a block
-- statement:
--   Throughout, $D\subseteq\mathbb R^d$ is a compact convex nonempty body with affine dimension $j=\dim\operatorname{aff}D$ and normalized relative volume $\sigma$ (Hausdorff measure of dimension $j$, conditioned on $D$). On a probability space with sub-$\sigma$-algebras $(\mathcal F_n)_{n\le T}$, increasing for $n<T$, the random affine field $Z_n(u)=u^\top V_n+c_n$ ($u\in D$) has $\mathcal F_n$-measurable $V_n\in\mathbb R^d$, $c_n\in\mathbb R$, and $J_n$ are $\mathcal F_n$-measurable alive events with $J_{n+1}\subseteq J_n$. Write $N_n=\max_D(-Z_n)$ and $\xi_n(u)=Z_{n+1}(u)-Z_n(u)$. The **field interface** $\mathrm{FI}(\beta,B,\ell,h,m_0)$ asks that $Z_n$ be a.s. bounded on $D$, that $N_n\ge0$ a.s., and that for $m_0\le n<T$ and $u\in D$, almost surely on $J_n$,
--   $$
--   \ell\le\mathbb E[\xi_n(u)\mid\mathcal F_n]\le h,\qquad |\xi_n(u)|\le3\beta_n+\frac{Z_n(u)+2N_n}{B},\qquad \mathbb E[\xi_n(u)^2\mid\mathcal F_n]\le10\beta_n+\frac{2(Z_n(u)+2N_n)^2}{B(n+1)} .
--   $$
--
--   Assume $\mathrm{FI}(\beta,B,0,h,m_0)$ holds (nonnegative drift) with $h\ge0$. Let $k\ge2$, $j\le4k$, $2^{20}\cdot4k\le B$, $b\ge0$, $\beta_n\ge1$, $\beta_n^2\le b^2(n+1)$, and let $W\in\mathbb N$ satisfy $W\ge1+1024(4k)^2/B$. Fix $v$, $m_0\le m\le N\le T$ and $1\le\lambda\le\rho$. Let $\bar Z=\mathrm{frz}(Z,A)$ be the field frozen at its first crossing after $v$, i.e. at the survival rule $A_s=J_s\cap\{s<v\text{ or }N_s\le\lambda\}$. Let $p_A$ bound $\mathbb P(\max_D|\bar Z_N|>\rho)$, and let $F_0$ bound $\mathbb E\int_D(-\bar Z_m)_+^{4k}d\sigma$. Then
--   $$
--   \mathbb P\big(\exists s\in[v,N]:\ \omega\in J_s,\ N_s>\lambda\big)\le p_A+\frac{2^{4k}4^{j}(\rho/\lambda)^{j}}{\lambda^{4k}}\Big(H_{\rm neg}(k,b,B)\,(N+1)^{3k}+\Big(\frac{N+1}{m+1}\Big)^{W}F_0\Big).
--   $$
--
--   The negative integral moment of the frozen field satisfies the linear recurrence (G.490) from time $m$ onward; Markov's inequality at the deterministic endpoint $N$, applied to the frozen negative maximum, controls the first crossing as in (G.423). Lemma J.11 converts the integral moment into the maximum on $\{\max_D|\bar Z_N|\le\rho\}$. This is the block-crossing bound used for the windows in Lemmas G.22, G.28 and G.29.
--
--   **Formalization Note** `Hneg k b B` is the particular-solution constant of the negative recurrence; rounds are 0-based.
-- source:
--   Zhao–Tan, Best-of-Both-Worlds FTRL for Linear Bandits: The Interplay of Information Acquisition, Corruption, and Geometry (STOC submission version; arXiv:2611.01299), Appendix G, proof of Lemma G.22, (G.423) (p.165), with Lemma G.25 (G.490) (p.171) and Lemma J.11 (p.211)

import Mathlib
import Definitions.Def_IAFTRL_LinEnv
import Definitions.Def_IAFTRL_GIAFTRL
import Definitions.Def_IAFTRL_G26_body
import Definitions.Def_IAFTRL_G26_run
import Definitions.Def_IAFTRL_G26_window

open MeasureTheory ProbabilityTheory Set IAFTRL Matrix J11
open G26
variable {d : ℕ} {Ω : Type*}
variable {D : Set (Fin d → ℝ)} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}
  {F : ℕ → MeasurableSpace Ω} {T : ℕ} {V : ℕ → Ω → (Fin d → ℝ)} {c : ℕ → Ω → ℝ}
  {J : ℕ → Set Ω} {β : ℕ → ℝ} {B lo hi : ℝ} {m0 : ℕ}

theorem G26.FI.cross_env [IsProbabilityMeasure μ] (I : FI D μ F T V c J β B 0 hi m0) (hhi : 0 ≤ hi)
    {k : ℕ} (hk : 2 ≤ k) (hjP : rdim D ≤ 4 * k) (hB : 2 ^ 20 * (4 * k : ℝ) ≤ B) {b : ℝ}
    (hb : 0 ≤ b) (hβ1 : ∀ n, 1 ≤ β n) (hβb : ∀ n, β n ^ 2 ≤ b ^ 2 * ((n : ℝ) + 1)) {W : ℕ}
    (hW : 1 + 1024 * (4 * k : ℝ) ^ 2 / B ≤ W) {v N m : ℕ} (hm0 : m0 ≤ m) (hmN : m ≤ N)
    (hN : N ≤ T) {lam ρ : ℝ} (hlam : 1 ≤ lam) (hlρ : lam ≤ ρ) {pA F0 : ℝ}
    (hpA : μ.real {ω | ρ < absMax D (frz V (crossA D V c J v lam) N ω)
      (frz c (crossA D V c J v lam) N ω)} ≤ pA)
    (hF0 : ∫ ω, Ff D (frz V (crossA D V c J v lam)) (frz c (crossA D V c J v lam)) (4 * k) m ω ∂μ
      ≤ F0) :
    μ.real {ω | ∃ s, v ≤ s ∧ s ≤ N ∧ ω ∈ J s ∧ lam < negMax D (V s ω) (c s ω)} ≤
      pA + 2 ^ (4 * k) * 4 ^ rdim D * (ρ / lam) ^ rdim D / lam ^ (4 * k) *
        (Hneg k b B * ((N : ℝ) + 1) ^ (3 * k) + (((N : ℝ) + 1) / ((m : ℝ) + 1)) ^ W * F0) := by sorry
