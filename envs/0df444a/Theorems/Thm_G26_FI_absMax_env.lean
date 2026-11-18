-- Prove2me | Theorems.Thm_G26_FI_absMax_env
-- name    : G26.FI.absMax_env
-- status  : Proved
-- author  : @Canzhe Zhao
-- created : 2026-11-18T00:30:26.830986+00:00
-- url     : https://prove2.me/theorems/1cd2b161-ecfe-4f5a-a73a-ef6fc3b771bc
-- title:
--   Absolute envelope of a field-interface affine field: E[1_J max_D |Z_n|^P] = O(n^P)
-- statement:
--   Throughout, $D\subseteq\mathbb R^d$ is a compact convex nonempty body with affine dimension $j=\dim\operatorname{aff}D$ and normalized relative volume $\sigma$ (Hausdorff measure of dimension $j$, conditioned on $D$). On a probability space with sub-$\sigma$-algebras $(\mathcal F_n)_{n\le T}$, increasing for $n<T$, the random affine field $Z_n(u)=u^\top V_n+c_n$ ($u\in D$) has $\mathcal F_n$-measurable $V_n\in\mathbb R^d$, $c_n\in\mathbb R$, and $J_n$ are $\mathcal F_n$-measurable alive events with $J_{n+1}\subseteq J_n$. Write $N_n=\max_D(-Z_n)$ and $\xi_n(u)=Z_{n+1}(u)-Z_n(u)$. The **field interface** $\mathrm{FI}(\beta,B,\ell,h,m_0)$ asks that $Z_n$ be a.s. bounded on $D$, that $N_n\ge0$ a.s., and that for $m_0\le n<T$ and $u\in D$, almost surely on $J_n$,
--   $$
--   \ell\le\mathbb E[\xi_n(u)\mid\mathcal F_n]\le h,\qquad |\xi_n(u)|\le3\beta_n+\frac{Z_n(u)+2N_n}{B},\qquad \mathbb E[\xi_n(u)^2\mid\mathcal F_n]\le10\beta_n+\frac{2(Z_n(u)+2N_n)^2}{B(n+1)} .
--   $$
--
--   Assume $\mathrm{FI}(\beta,B,\ell,h,0)$ holds with $-2\le\ell$ and $h\le2$. Let $P\ge4$ be even with $j\le P$, $2^{20}P\le B$, $\beta_n>0$ and $\beta_n\le b(n+1)$ for all $n$, and suppose the field starts at zero: $\int_DZ_0^P\,d\sigma=0$ for every $\omega$. Then for every $n\le T$,
--   $$
--   \mathbb E\Big[\mathbf 1_{J_n}\big(\max_{u\in D}|Z_n(u)|\big)^P\Big]\le2^P\,4^{j}\,C_{\rm abs}(P,b,B)\,(n+1)^P,
--   $$
--   where $C_{\rm abs}(P,b,B)=\max\{0,K_{\rm abs}(P,b,B)/(P-3-1152P^2/B)\}$ (`Cabs P b B 0`).
--
--   The absolute integral moment $G_n=\int_D|Z_n|^Pd\sigma$ satisfies the recurrence (G.488), whose solution starting at zero is $O(n^P)$; Lemma J.11 converts the integral moment of the affine function into its maximum over $D$ at the cost $2^P4^j$. This is the envelope $\mathbb E[\max|X_s|^P]\le R^Ps^P$ of Lemmas G.15, G.28 and G.30.
--
--   **Formalization Note** Rounds are 0-based; the constants are explicit.
-- source:
--   Zhao–Tan, Best-of-Both-Worlds FTRL for Linear Bandits: The Interplay of Information Acquisition, Corruption, and Geometry (STOC submission version; arXiv:2611.01299), Appendix G, Lemma G.25 (G.488) and the bound E[G_s] ≤ C_G s^P (p.170), combined with Lemma J.11 (p.211)

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

theorem G26.FI.absMax_env [IsProbabilityMeasure μ] (I : FI D μ F T V c J β B lo hi 0)
    (hlo : -2 ≤ lo) (hhi : hi ≤ 2) {P : ℕ} (hP : 4 ≤ P) (hev : Even P) (hjP : rdim D ≤ P)
    (hB : 2 ^ 20 * (P : ℝ) ≤ B) {b : ℝ} (hβ : ∀ n, 0 < β n)
    (hβb : ∀ n, β n ≤ b * ((n : ℝ) + 1)) (h0 : ∀ ω, Gf D V c P 0 ω = 0) {n : ℕ} (hn : n ≤ T) :
    ∫ ω, (J n).indicator (fun ω => absMax D (V n ω) (c n ω) ^ P) ω ∂μ ≤
      2 ^ P * 4 ^ rdim D * Cabs P b B 0 * ((n : ℝ) + 1) ^ P := by sorry
