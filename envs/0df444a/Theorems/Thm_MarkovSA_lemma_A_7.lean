-- Prove2me | Theorems.Thm_MarkovSA_lemma_A_7
-- name    : MarkovSA.lemma_A_7
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:52:16.647199+00:00
-- url     : https://prove2.me/theorems/b5182c35-3584-462a-8fcc-19cf3d5df8d5
-- title:
--   Lemma A.7 — evaluation of (19) for $\alpha_k=\alpha/(k+h)$ (corrected: $t_k\ge1$ in admissibility)
-- statement:
--   Let $P$ satisfy Assumption 2.3, $A_1,A_2>0$, $A=A_1+A_2+1$, $\varphi_1,\varphi_2,\varphi_3$ from admissible smoothing data, and let $(\alpha,h)$ be admissible for $\alpha_k=\alpha/(k+h)$ with mixing times $t_k$ and index $K$ (least $K_0$ with $t_k\le k$ for all $k\ge K_0$). For $c_1,c_2\ge0$ write
--
--   $$
--   R_k=\varphi_1c_1\prod_{j=K}^{k-1}(1-\varphi_2\alpha_j)+\varphi_3c_2\sum_{i=K}^{k-1}\alpha_i\alpha_{i-t_i,i-1}\prod_{j=i+1}^{k-1}(1-\varphi_2\alpha_j),
--   $$
--
--   the right side of Eq. (19). Then for all $k\ge K$:
--
--   1. if $\alpha<1/\varphi_2$: $\ R_k\le\varphi_1c_1\Big(\dfrac{K+h}{k+h}\Big)^{\varphi_2\alpha}+\dfrac{8\varphi_3c_2\alpha^2}{1-\varphi_2\alpha}\cdot\dfrac{t_k}{(k+h)^{\varphi_2\alpha}}$;
--   2. if $\alpha=1/\varphi_2$: $\ R_k\le\varphi_1c_1\dfrac{K+h}{k+h}+8\varphi_3c_2\alpha^2\cdot\dfrac{t_k\log(k+h)}{k+h}$;
--   3. if $\alpha>1/\varphi_2$: $\ R_k\le\varphi_1c_1\Big(\dfrac{K+h}{k+h}\Big)^{\varphi_2\alpha}+\dfrac{8e\varphi_3c_2\alpha^2}{\varphi_2\alpha-1}\cdot\dfrac{t_k}{k+h}$.
--
--   Differences from the source:
--   - reading: a bound on $\mathbb E[\|x_k-x^*\|_c^2]$ → the same bound on the right side $R_k$ of (19); reason: the proof (Appendix A.3.6–A.3.7) bounds exactly $R_k$; with Theorem A.1 (2) this gives the printed inequality, and the probabilistic part is left to Theorem A.1
--   - reading: $K=\min\{k\ge0:k\ge t_k\}$, then used as if $t_k\le k$ for all $k\ge K$ → $K$ = least $K_0$ with $t_k\le k$ for every $k\ge K_0$; reason: with the printed $K$ the right side can contain a negative index (two-state chain whose stepsize drops by a factor 8 after step $m$); the proof uses the read $K$
--   - reading: Condition 2.1 (2), (3): 'there exists a threshold $\bar h$' for $h$ (specified in App. A.2) → admissibility: Condition A.1, $t_k\ge1$, $\alpha_{k-t_k}\le2\alpha_k$, and $h\ge[2\xi/(\varphi_2\alpha)]^{1/(1-\xi)}$ for $\xi<1$; reason: Theorem A.3 prints a weaker condition on $\bar h$ than its proof (pp.29–30) establishes and uses; these are the proof's conditions
--   - correction: $t_k\ge0$ → admissibility includes $t_k\ge1$; reason: correction C1 (see Theorem A.1)
--   - encoding: unique stationary distribution $\mu$ → $\mu$ stationary; uniqueness not assumed; reason: uniqueness follows from the geometric decay of Assumption 2.3
--   - encoding: $\mathbb R^d$ with an arbitrary norm $\|\cdot\|_c$ → a finite-dimensional real normed space $E$ with its norm; reason: the same spaces up to linear isometry; $d$ does not appear in the statement
--   - reading: $\|\cdot\|_s$, $\ell_{cs}$, $u_{cs}$, $\theta$ 'properly chosen' → any smoothing data meeting the conditions of p.24; reason: the paper fixes one such choice without specifying it; the claim holds for each
--   - generalization: the constants $c_1,c_2$ of Theorem 2.1 → any $c_1,c_2\ge0$; reason: the proof uses only their nonnegativity; the printed constants are a special case
--   - reading: $\ell_{cs}\|\cdot\|_c\le\|\cdot\|_c\le u_{cs}\|\cdot\|_s$ (as printed, p.24) → $\ell_{cs}\|\cdot\|_s\le\|\cdot\|_c\le u_{cs}\|\cdot\|_s$; reason: the left norm is a misprint: read literally it only says $\ell_{cs}\le1$, while pp.30 and 34 use $\|\cdot\|_s\le\|\cdot\|_c/\ell_{cs}$
--   - encoding: the norm $\|\cdot\|_s$ → a function with the norm axioms; reason: same objects
-- source:
--   Chen, Maguluri, Shakkottai & Shanmugam, A Lyapunov Theory for Finite-Sample Guarantees of Markovian Stochastic Approximation, arXiv:2102.01567v4, Lemma A.7, p.29

import Mathlib
import Definitions.Def_mm_mixing
import Definitions.Def_MarkovSA_Assumption23
import Definitions.Def_MarkovSA_IsSmoothingData
import Definitions.Def_MarkovSA_phi1
import Definitions.Def_MarkovSA_phi2
import Definitions.Def_MarkovSA_phi3
import Definitions.Def_MarkovSA_Aconst
import Definitions.Def_MarkovSA_Admissible
import Definitions.Def_MarkovSA_Kidx
import Definitions.Def_MarkovSA_winSum
open MeasureTheory

namespace MarkovSA

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {𝒴 : Type*} [Fintype 𝒴] [DecidableEq 𝒴]

/-- **Lemma A.7** (Chen, Maguluri, Shakkottai & Shanmugam, arXiv:2102.01567v4, §A.2, p.29), the evaluation of the right side of Eq. (19) for `α_k = α/(k + h)`.
For admissible `(α, h)` and all `k ≥ K`, the right side
`R_k = φ₁c₁ ∏_{j=K}^{k−1}(1 − φ₂α_j) + φ₃c₂ Σ_{i=K}^{k−1} α_iα_{i−t_i,i−1} ∏_{j=i+1}^{k−1}(1 − φ₂α_j)` satisfies
`R_k ≤ φ₁c₁((K + h)/(k + h))^{φ₂α} + (8φ₃c₂α²/(1 − φ₂α))·t_k/(k + h)^{φ₂α}` if `α < 1/φ₂`;
`R_k ≤ φ₁c₁(K + h)/(k + h) + 8φ₃c₂α²·t_k log(k + h)/(k + h)` if `α = 1/φ₂`;
`R_k ≤ φ₁c₁((K + h)/(k + h))^{φ₂α} + (8eφ₃c₂α²/(φ₂α − 1))·t_k/(k + h)` if `α > 1/φ₂`;
for all `c₁, c₂ ≥ 0`.

**Formalization Note.** Stated for the deterministic right side of (19), which is what the proof (Appendix A.3.6)
bounds; with Theorem A.1 (2) it gives the printed bound on `E[‖x_k − x*‖_c²]`. `K` is read by R2. -/
theorem lemma_A_7 (P : Matrix 𝒴 𝒴 ℝ) (μ : 𝒴 → ℝ) (C σ : ℝ) (hchain : Assumption23 P μ C σ)
    (β A₁ A₂ : ℝ) (hA₁ : 0 < A₁) (hA₂ : 0 < A₂)
    (s : E → ℝ) (L ℓ u θ : ℝ) (hsm : IsSmoothingData s L ℓ u θ β)
    (a h : ℝ) (ha : 0 < a) (hh : 0 < h) (hadm : Admissible P μ (phi2 β ℓ u θ) (phi3 L ℓ u θ) (Aconst A₁ A₂) a 1 h)
    (c₁ c₂ : ℝ) (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂) (k : ℕ) (hk : Kidx (stepMix P μ (polyStep a h 1)) ≤ k) :
    (a < 1 / phi2 β ℓ u θ →
      phi1 ℓ u θ * c₁ * ∏ j ∈ Finset.Ico (Kidx (stepMix P μ (polyStep a h 1))) k, (1 - phi2 β ℓ u θ * polyStep a h 1 j) +
        phi3 L ℓ u θ * c₂ * ∑ i ∈ Finset.Ico (Kidx (stepMix P μ (polyStep a h 1))) k,
          polyStep a h 1 i * winSum (polyStep a h 1) (i - stepMix P μ (polyStep a h 1) i) i * ∏ j ∈ Finset.Ico (i + 1) k, (1 - phi2 β ℓ u θ * polyStep a h 1 j) ≤
        phi1 ℓ u θ * c₁ * (((Kidx (stepMix P μ (polyStep a h 1)) : ℕ) + h) / ((k : ℝ) + h)) ^ (phi2 β ℓ u θ * a) +
          8 * phi3 L ℓ u θ * c₂ * a ^ 2 / (1 - phi2 β ℓ u θ * a) * ((stepMix P μ (polyStep a h 1) k : ℝ) / ((k : ℝ) + h) ^ (phi2 β ℓ u θ * a))) ∧
    (a = 1 / phi2 β ℓ u θ →
      phi1 ℓ u θ * c₁ * ∏ j ∈ Finset.Ico (Kidx (stepMix P μ (polyStep a h 1))) k, (1 - phi2 β ℓ u θ * polyStep a h 1 j) +
        phi3 L ℓ u θ * c₂ * ∑ i ∈ Finset.Ico (Kidx (stepMix P μ (polyStep a h 1))) k,
          polyStep a h 1 i * winSum (polyStep a h 1) (i - stepMix P μ (polyStep a h 1) i) i * ∏ j ∈ Finset.Ico (i + 1) k, (1 - phi2 β ℓ u θ * polyStep a h 1 j) ≤
        phi1 ℓ u θ * c₁ * (((Kidx (stepMix P μ (polyStep a h 1)) : ℕ) + h) / ((k : ℝ) + h)) +
          8 * phi3 L ℓ u θ * c₂ * a ^ 2 * ((stepMix P μ (polyStep a h 1) k : ℝ) * Real.log ((k : ℝ) + h) / ((k : ℝ) + h))) ∧
    (1 / phi2 β ℓ u θ < a →
      phi1 ℓ u θ * c₁ * ∏ j ∈ Finset.Ico (Kidx (stepMix P μ (polyStep a h 1))) k, (1 - phi2 β ℓ u θ * polyStep a h 1 j) +
        phi3 L ℓ u θ * c₂ * ∑ i ∈ Finset.Ico (Kidx (stepMix P μ (polyStep a h 1))) k,
          polyStep a h 1 i * winSum (polyStep a h 1) (i - stepMix P μ (polyStep a h 1) i) i * ∏ j ∈ Finset.Ico (i + 1) k, (1 - phi2 β ℓ u θ * polyStep a h 1 j) ≤
        phi1 ℓ u θ * c₁ * (((Kidx (stepMix P μ (polyStep a h 1)) : ℕ) + h) / ((k : ℝ) + h)) ^ (phi2 β ℓ u θ * a) +
          8 * Real.exp 1 * phi3 L ℓ u θ * c₂ * a ^ 2 / (phi2 β ℓ u θ * a - 1) * ((stepMix P μ (polyStep a h 1) k : ℝ) / ((k : ℝ) + h))) := by sorry

end MarkovSA
