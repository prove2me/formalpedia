-- Prove2me | Theorems.Thm_MarkovSA_thresholds_exist
-- name    : MarkovSA.thresholds_exist
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:51:55.827768+00:00
-- url     : https://prove2.me/theorems/3c374e52-b40a-4c41-9208-94d11ac3f53b
-- title:
--   Theorem A.3 (proof), pp.28–29 — the stepsize thresholds of Condition 2.1 exist (corrected: $\delta\le C/\sigma$; $|\mathcal Y|\ge2$)
-- statement:
--   Let $P$ satisfy Assumption 2.3 with $C,\sigma$ on a set $\mathcal Y$ with at least two points, let $A_1,A_2>0$, $A=A_1+A_2+1$, let $\varphi_2,\varphi_3$ come from admissible smoothing data, and put $T=\min\big(\varphi_2/(\varphi_3A^2),1/(4A)\big)$. Then:
--
--   1. $t_\delta\le\dfrac{\log(1/\delta)+\log(C/\sigma)}{\log(1/\sigma)}$ for every $\delta\in(0,C/\sigma]$;
--   2. there is $\bar\alpha\in(0,1)$ with $\alpha t_\alpha\le T$ for all $\alpha\in(0,\bar\alpha)$ (Condition 2.1 (1));
--   3. for every $\alpha>0$ there is $\bar h>0$ such that $(\alpha,h)$ is admissible for $\alpha_k=\alpha/(k+h)$ whenever $h\ge\bar h$ (Condition 2.1 (2));
--   4. for every $\xi\in(0,1)$ and $\alpha>0$ there is $\bar h>0$ such that $(\alpha,h)$ is admissible for $\alpha_k=\alpha/(k+h)^\xi$ whenever $h\ge\bar h$ (Condition 2.1 (3)).
--
--   The thresholds depend only on the chain, $A$ and $\varphi_2,\varphi_3$, never on the operator, the noise or the initial point.
--
--   Differences from the source:
--   - correction: $t_\alpha\le(\log(1/\alpha)+\log(C/\sigma))/\log(1/\sigma)$ for the stepsize $\alpha$ (and 'for any $\delta>0$', remark p.6) → for $0<\delta\le C/\sigma$; reason: the last step needs $\log(C/\delta)\ge\log\sigma$; counterexample: two-point i.i.d. uniform chain, $C=\frac12$, $\sigma=0.9$, $\delta=0.6$: $t_\delta=0$ but the right side is $\approx-0.73$; the proof's $\alpha<\bar\alpha$ lie in this range
--   - correction: $\mathcal Y$ any finite set → $\mathcal Y$ has at least two points, and admissibility includes $t_k\ge1$; reason: correction C1 of the goal: with one point $t_\delta=0$ and the bounds fail (see Theorem 2.1)
--   - reading: Condition 2.1 (2), (3): 'there exists a threshold $\bar h$' for $h$ (specified in App. A.2) → admissibility: Condition A.1, $t_k\ge1$, $\alpha_{k-t_k}\le2\alpha_k$, and $h\ge[2\xi/(\varphi_2\alpha)]^{1/(1-\xi)}$ for $\xi<1$; reason: Theorem A.3 prints a weaker condition on $\bar h$ than its proof (pp.29–30) establishes and uses; these are the proof's conditions
--   - encoding: unique stationary distribution $\mu$ → $\mu$ stationary; uniqueness not assumed; reason: uniqueness follows from the geometric decay of Assumption 2.3
--   - encoding: $\mathbb R^d$ with an arbitrary norm $\|\cdot\|_c$ → a finite-dimensional real normed space $E$ with its norm; reason: the same spaces up to linear isometry; $d$ does not appear in the statement
--   - reading: $\|\cdot\|_s$, $\ell_{cs}$, $u_{cs}$, $\theta$ 'properly chosen' → any smoothing data meeting the conditions of p.24; reason: the paper fixes one such choice without specifying it; the claim holds for each
--   - reading: $\ell_{cs}\|\cdot\|_c\le\|\cdot\|_c\le u_{cs}\|\cdot\|_s$ (as printed, p.24) → $\ell_{cs}\|\cdot\|_s\le\|\cdot\|_c\le u_{cs}\|\cdot\|_s$; reason: the left norm is a misprint: read literally it only says $\ell_{cs}\le1$, while pp.30 and 34 use $\|\cdot\|_s\le\|\cdot\|_c/\ell_{cs}$
--   - encoding: the norm $\|\cdot\|_s$ → a function with the norm axioms; reason: same objects
-- source:
--   Chen, Maguluri, Shakkottai & Shanmugam, A Lyapunov Theory for Finite-Sample Guarantees of Markovian Stochastic Approximation, arXiv:2102.01567v4, proof of Theorem A.3, pp.28–29, and Condition 2.1, p.6

import Mathlib
import Definitions.Def_mm_mixing
import Definitions.Def_MarkovSA_Assumption23
import Definitions.Def_MarkovSA_IsSmoothingData
import Definitions.Def_MarkovSA_phi2
import Definitions.Def_MarkovSA_phi3
import Definitions.Def_MarkovSA_Aconst
import Definitions.Def_MarkovSA_Admissible
open MeasureTheory

namespace MarkovSA

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {𝒴 : Type*} [Fintype 𝒴] [DecidableEq 𝒴]

/-- **Existence of the stepsize thresholds** (Chen, Maguluri, Shakkottai & Shanmugam, arXiv:2102.01567v4, proof of Theorem A.3, pp.28–29; Condition 2.1, p.6),
for a chain with at least two states (C1). With `T = min(φ₂/(φ₃A²), 1/(4A))`:
1. `t_δ ≤ (log(1/δ) + log(C/σ))/log(1/σ)` for `0 < δ ≤ C/σ` (corrected range; the proof uses it for `δ = α ∈ (0, ᾱ)`);
2. there is `ᾱ ∈ (0, 1)` with `αt_α ≤ T` for all `α ∈ (0, ᾱ)` (Condition 2.1 (1));
3. for each `α > 0` there is `h̄ > 0` such that `(α, h)` is admissible for `ξ = 1` for all `h ≥ h̄` (Condition 2.1 (2));
4. for each `ξ ∈ (0, 1)` and `α > 0` there is `h̄ > 0` such that `(α, h)` is admissible for `ξ` for all `h ≥ h̄`
(Condition 2.1 (3)).

**Formalization Note.** "Admissible" (`Admissible`, reading R4) is Condition A.1 together with `t_k ≥ 1`,
`α_{k−t_k} ≤ 2α_k` and, for `ξ < 1`, `h ≥ [2ξ/(φ₂α)]^{1/(1−ξ)}`: the conditions the proof establishes for
`h ≥ h̄`. The thresholds depend only on the chain, `A` and `φ₂, φ₃`. -/
theorem thresholds_exist [Nontrivial 𝒴] (P : Matrix 𝒴 𝒴 ℝ) (μ : 𝒴 → ℝ) (C σ : ℝ) (hchain : Assumption23 P μ C σ)
    (β A₁ A₂ : ℝ) (hA₁ : 0 < A₁) (hA₂ : 0 < A₂)
    (s : E → ℝ) (L ℓ u θ : ℝ) (hsm : IsSmoothingData s L ℓ u θ β) :
    (∀ δ : ℝ, 0 < δ → δ ≤ C / σ →
      (MarkovMixing.mixingTime P μ δ : ℝ) ≤ (Real.log (1 / δ) + Real.log (C / σ)) / Real.log (1 / σ)) ∧
    (∃ αbar : ℝ, 0 < αbar ∧ αbar < 1 ∧ ∀ a : ℝ, 0 < a → a < αbar →
      a * (MarkovMixing.mixingTime P μ a : ℝ) ≤ min (phi2 β ℓ u θ / (phi3 L ℓ u θ * Aconst A₁ A₂ ^ 2)) (1 / (4 * Aconst A₁ A₂))) ∧
    (∀ a : ℝ, 0 < a → ∃ hbar : ℝ, 0 < hbar ∧ ∀ h : ℝ, hbar ≤ h → Admissible P μ (phi2 β ℓ u θ) (phi3 L ℓ u θ) (Aconst A₁ A₂) a 1 h) ∧
    (∀ ξ : ℝ, 0 < ξ → ξ < 1 → ∀ a : ℝ, 0 < a →
      ∃ hbar : ℝ, 0 < hbar ∧ ∀ h : ℝ, hbar ≤ h → Admissible P μ (phi2 β ℓ u θ) (phi3 L ℓ u θ) (Aconst A₁ A₂) a ξ h) := by sorry

end MarkovSA
