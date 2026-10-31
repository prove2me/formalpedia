-- Prove2me | Theorems.Thm_InfoShareH2_proposition_5
-- name    : InfoShareH2.proposition_5
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:29:51.036498+00:00
-- url     : https://prove2.me/theorems/32aba108-4681-4b50-864f-380bb47f4d5d
-- title:
--   Proposition 5 — inventory z-transform $\psi_I=(z\tilde\psi-1)/(1-z)$ and $\sigma_I^2=\int f_I$ (corrected: factor $\sigma_\epsilon^2$ in (36)–(37))
-- statement:
--   Let $\epsilon=(\epsilon_t)_{t\in\mathbb Z}$ be a Gaussian white noise with variance $\sigma_\epsilon^2>0$ on a probability space, $d\in\mathbb R$, demand $D_t=d+\epsilon_t$, and orders $O_t=d+\sum_{n\ge0}\tilde\psi_n\epsilon_{t-n}$ with $\tilde\psi\in\tilde\Psi$. Let the inventory satisfy $I_t=I_{t-1}+O_{t-1}-D_t$ for $t\ge1$ from a square-integrable $I_0$, and let
--
--   $$\tilde I_0=I_0+D_0-d-\sum_{n\ge1}\Bigl(\sum_{k<n}\tilde\psi_k-1\Bigr)\epsilon_{-n}.$$
--
--   Write $J_t=I_t-\tilde I_0$, $g_k=\sum_{j<k}\tilde\psi_j-1$, $\psi_I(z)=\frac{z\tilde\psi(z)-1}{1-z}$ and $f_I(\lambda)=\frac{\sigma_\epsilon^2}{2\pi}|\psi_I(e^{-i\lambda})|^2$. Then:
--
--   1. $J_t=\sum_{k\ge0}g_k\epsilon_{t-k}$ in $L^2$ for $t\ge1$;
--   2. $(J_t)_{t\ge1}$ is weakly stationary: its mean is constant and $\operatorname{Cov}(J_s,J_{s+h})$ depends only on $h$;
--   3. its z-transform is $\sum_kg_kz^k=\psi_I(z)$ for $|z|<1$, and on the circle its boundary value is $\psi_I(e^{-i\lambda})$ for almost every $\lambda\ne0$;
--   4. $f_I$ is its spectral density: $\operatorname{Cov}(J_s,J_{s+h})=\int_{-\pi}^{\pi}e^{ih\lambda}f_I(\lambda)\,d\lambda$;
--   5. $$\operatorname{Var}(J_t)=\int_{-\pi}^{\pi}f_I(\lambda)\,d\lambda=\frac{\sigma_\epsilon^2}{2\pi}\int_{-\pi}^{\pi}\Bigl|\frac{z\tilde\psi(z)-1}{1-z}\Bigr|^2d\lambda=\sigma_I^2(\tilde\psi),\qquad z=e^{-i\lambda}.$$
--
--   This moves the inventory variance from the time domain to the frequency domain, where the Hardy-space factorization applies.
--
--   Differences from the source:
--   - correction: (36) f_I = (1/2π)ψ_I(e^{−iλ})ψ_I(e^{iλ}); (37) var(I_t − Ĩ_0) = (1/2π)∫|(zψ̃(z) − 1)/(1 − z)|² → f_I = (σ_ε²/2π)|ψ_I(e^{−iλ})|²; var(J_t) = ∫ f_I = σ²_I(ψ̃); reason: the printed forms omit σ_ε²: for σ_ε = 2 and ψ̃ = (1, 0, …) ∈ Ψ̃, J_t = −ε_t has variance 4 while the printed right side of (37) is 1
--   - reading: "ψ̃ ∈ H² corresponding to an ordering policy satisfying Assumption 1" → ψ̃ ∈ Ψ̃ with a Gaussian white noise of variance σ_ε² > 0; reason: Assumption 1(a)–(b)
--   - reading: "weakly stationary" → constant mean and lag-dependent covariance of J_t for t ≥ 1; reason: the inventory recursion (2) starts at t = 1
--   - reading: "spectral density f_I" → Cov(J_s, J_{s+h}) = ∫ e^{ihλ} f_I(λ) dλ; reason: definition of a spectral density
--   - encoding: random variables, MA(∞) series, z-transform on T, ψ_I(e^{−iλ})ψ_I(e^{iλ}) → elements of L²(P), unordered sums in L², radial limits a.e., |ψ_I(e^{−iλ})|²; reason: Lean representation; real coefficients
-- source:
--   Caldentey–Giloni–Hurvich–Zhang, Information Design and Sharing in Supply Chains, SSRN 4319721 (v. 2024-01-20), https://ssrn.com/abstract=4319721, Proposition 5, p.26, (36)–(37) (proof §9.10, pp.45–46); (2) p.9, (4)–(5) p.10, (7) p.11

import Mathlib
import Definitions.Def_InfoShareH2_Model
import Definitions.Def_InfoShareH2_Hardy
import Definitions.Def_InfoShareH2_Process

open Filter Topology MeasureTheory Complex ProbabilityTheory

set_option autoImplicit false

namespace InfoShareH2

/-- **Proposition 5 (inventory variance in the frequency domain).**
SSRN 4319721 (v. 2024-01-20), Proposition 5, p.26, (36)–(37) (proof §9.10, pp.45–46). "For any
`ψ̃ ∈ H²` corresponding to an ordering policy `{O_t}` satisfying Assumption 1, the initialized
inventory `{I_t − Ĩ_0}` is weakly stationary, and it has z-transform and spectral density
`ψ_I(z) = (zψ̃(z) − 1)/(1 − z)`, `z ∈ D ∪ T∖{1}`,
`f_I(e^{−iλ}) = (1/2π) ψ_I(e^{−iλ}) ψ_I(e^{iλ})`, `λ ∈ [−π, π]`. The retailer's inventory variance in
(8) can be written as follows, `σ²_I(ψ̃) = var(I_t − Ĩ_0) = ∫_{−π}^{π} f_I(e^{−iλ}) dλ =
(1/2π) ∫_{−π}^{π} |(zψ̃(z) − 1)/(1 − z)|² dλ`, where `z = e^{−iλ}`."

Setting: Gaussian white noise `ε` (Assumption 1(a)), `D_t = d + ε_t` (4), orders `O_t` (5) in `L²`,
inventory `I_t = I_{t−1} + O_{t−1} − D_t` for `t ≥ 1` (2) from a given `I_0 ∈ L²`, and
`Ĩ_0 = I_0 + D_0 − d − ∑_{n≥1} (∑_{k<n} ψ̃_k − 1) ε_{−n}` (7). The z-transform of `{I_t − Ĩ_0}` is
that of its MA(∞) coefficients `g_k = ∑_{j<k} ψ̃_j − 1` (§9.10). On `T` it is the radial limit.

**Formalization Note** (corrected) `f_I = (σ_ε²/2π)|ψ_I|²`: the printed (36)–(37) omit the factor
`σ_ε²` (counterexample `σ_ε = 2`, `ψ̃ = (1, 0, …)`: `var(I_t − Ĩ_0) = 4` while the printed right side
of (37) is `1`); with it, `∫ f_I = σ²_I(ψ̃)` of (8). For real coefficients
`ψ_I(e^{−iλ})ψ_I(e^{iλ}) = |ψ_I(e^{−iλ})|²`. "Weakly stationary" is: for `t ≥ 1`, `I_t − Ĩ_0` has
constant mean and lag-dependent covariance. The spectral density property is
`Cov(J_s, J_{s+h}) = ∫ e^{ihλ} f_I dλ`. Random variables are elements of `L²(P)`. -/
theorem proposition_5 {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (σε : ℝ) (hσε : 0 < σε) (d : ℝ) (ε : ℤ → Ω → ℝ) (hε : IsGaussianWhiteNoise P σε ε)
    (ψ : ℕ → ℝ) (hψ : ψ ∈ PsiTilde) (Inv : ℕ → Lp ℝ 2 P)
    (hInv : ∀ t : ℕ, Inv (t + 1) =
      Inv t + orderL2 P ψ d ε t - toL2 P (fun ω => d + ε ((t : ℤ) + 1) ω)) :
    let Itil0 : Lp ℝ 2 P := Inv 0 + toL2 P (ε 0) -
      ∑' n : ℕ, (partialSum ψ (n + 1) - 1) • toL2 P (ε (-((n : ℤ) + 1)))
    let g : ℕ → ℝ := fun k => partialSum ψ k - 1
    let J : ℕ → Lp ℝ 2 P := fun t => Inv t - Itil0
    let fI : ℝ → ℝ := fun lam => σε ^ 2 / (2 * Real.pi) *
      ‖(exp (-(lam : ℂ) * I) * boundary (ofRealSeq ψ) lam - 1) / (1 - exp (-(lam : ℂ) * I))‖ ^ 2
    (∀ t : ℕ, 1 ≤ t → HasSum (fun k : ℕ => g k • toL2 P (ε ((t : ℤ) - k))) (J t)) ∧
    (∀ s t : ℕ, 1 ≤ s → 1 ≤ t → ∫ ω, J s ω ∂P = ∫ ω, J t ω ∂P) ∧
    (∀ s t h : ℕ, 1 ≤ s → 1 ≤ t →
      covariance (J s) (J (s + h)) P = covariance (J t) (J (t + h)) P) ∧
    (∀ z ∈ Disk, zTransform (ofRealSeq g) z =
      (z * zTransform (ofRealSeq ψ) z - 1) / (1 - z)) ∧
    (∀ᵐ lam ∂(volume.restrict (Set.Ioc (-Real.pi) Real.pi)), lam ≠ 0 →
      boundary (ofRealSeq g) lam = (exp (-(lam : ℂ) * I) * boundary (ofRealSeq ψ) lam - 1) /
        (1 - exp (-(lam : ℂ) * I))) ∧
    (∀ s h : ℕ, 1 ≤ s → ((covariance (J s) (J (s + h)) P : ℝ) : ℂ) =
      ∫ lam in (-Real.pi)..Real.pi, exp ((h : ℂ) * (lam : ℂ) * I) * (fI lam : ℂ)) ∧
    (∀ t : ℕ, 1 ≤ t → variance (J t) P = ∫ lam in (-Real.pi)..Real.pi, fI lam) ∧
    (∫ lam in (-Real.pi)..Real.pi, fI lam) = invVar σε ψ := by sorry

end InfoShareH2
