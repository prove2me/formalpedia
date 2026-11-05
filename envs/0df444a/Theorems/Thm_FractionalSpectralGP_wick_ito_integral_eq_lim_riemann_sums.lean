-- Prove2me | Theorems.Thm_FractionalSpectralGP_wick_ito_integral_eq_lim_riemann_sums
-- name    : FractionalSpectralGP.wick_ito_integral_eq_lim_riemann_sums
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:31:25.450035+00:00
-- url     : https://prove2.me/theorems/e67cb253-e4f9-4260-9629-d9d2cd69b7e6
-- title:
--   Theorem 7.1 — $\int_a^bY\diamond W_\sigma\,dt=\lim_{|\Delta|\to0}\sum_kY(t_k)\diamond(X_\sigma(t_{k+1})-X_\sigma(t_k))$ in $\mathcal H'_p$
-- statement:
--   Let $(\sigma,(\lambda_n))$ be a spectral setting, $(h_n)$ a real orthonormal basis of $L^2(\mathbb R,dx)$, $P$ the white noise measure with the isometry $f\mapsto\widetilde f$, and $X_\sigma$, $W_\sigma$ the processes (6.2) and (6.4). Let $a<b$ and let $Y(t)$, $t\in[a,b]$, be an $S_{-1}$-valued function, continuous in the strong topology of $S_{-1}$. Then there exists $p\in\mathbb N$ such that
--
--   1. $Y(t)\diamond W_\sigma(t)\in\mathcal H'_p$ for every $t\in[a,b]$, and $t\mapsto Y(t)\diamond W_\sigma(t)$ is continuous from $[a,b]$ into $\mathcal H'_p$; and
--   2. in the norm of $\mathcal H'_p$,
--   $$
--   \int_a^bY(t)\diamond W_\sigma(t)\,dt=\lim_{|\Delta|\to0}\sum_{k=0}^{n-1}Y(t_k)\diamond\big(X_\sigma(t_{k+1})-X_\sigma(t_k)\big),
--   $$
--   where $\Delta:a=t_0<t_1<\dots<t_n=b$ ranges over partitions of $[a,b]$ and $|\Delta|=\max_k(t_{k+1}-t_k)$: for every $\varepsilon>0$ there is $\delta>0$ such that every partition with $|\Delta|<\delta$ has its Riemann sum in $\mathcal H'_p$ within distance $\varepsilon$ of the integral.
--
--   The Wick–Itô integral against the derivative process is therefore the limit of Wick–Riemann sums of the process itself, in one Hilbert space $\mathcal H'_p$, for every singular spectral measure in the class.
--
--   **Formalization Note** One $p\ge1$ serves both clauses and all partitions. The integral is the Bochner integral of the continuous $\mathcal H'_p$-valued map of clause 1. $W_\sigma(t)$ and the increments of $X_\sigma$ enter $S_{-1}$ through their chaos coefficients.
--
--   Differences from the source:
--   - generalization: σ in the paper's class (orthonormal basis e^{iλ_n u}, λ_n ∈ πℕ₀, the measures σ_m) → any spectral setting: finite σ on [−1/2, 1/2], (e_{λ_n}) an orthonormal basis, λ_0 = 0; reason: no proof uses λ_n ∈ πℕ₀; the paper's measures are spectral settings
--   - generalization: h_n the Hermite functions → any real-valued orthonormal basis (h_n) of L²(ℝ, dx); reason: the proofs use only that (h_n) is a real orthonormal basis; the Hermite functions are one
--   - generalization: real Schwartz space and real white noise space → complex-valued Schwartz functions, L²(ℝ; ℂ), L²(P; ℂ) and complex chaos coefficients; reason: restricting to real functions gives the page's statement
--   - encoding: P from the Bochner–Minlos theorem, f ↦ f̃ the extension of (4.2) → P and ι parameters satisfying (4.1) and (4.2); reason: Minlos is not in Mathlib; (4.1) determines P and eq_4_2_isometry gives exactly one ι
--   - encoding: formal series Σ f_α H_α and the norm ‖·‖_k of H′_k → coefficient families ℓ → ℂ and the ℓ²-norm of (f_α (2ℕ)^{−kα/2}); reason: the defining isometry of H′_k; same objects
--   - encoding: multi-indices α = (α_1, α_2, …) with weight 2k at coordinate k → α : ℕ →₀ ℕ, coordinate n carries Z_n and weight 2(n + 1); reason: index shift k = n + 1; same objects
--   - reading: Q_σ 1_{[0,t]} for every real t → the extended Q_σ at f_t(u) = ∫₀ᵗ e^{iux} dx (oriented integral); reason: (6.2) is stated for all t, so 1_{[0,t]} means −1_{[t,0]} for t < 0; f_t is the transform of the indicator, the printed χ_t differs by the factor i
--   - encoding: continuous in the strong topology of S_{−1} → uniform convergence of ⟨Y(s) − Y(t), g⟩ → 0 on bounded subsets of S₁, at every t ∈ [a, b]; reason: the strong dual topology of S_{−1} = S₁', which for this DFS space is the inductive limit topology
--   - encoding: p ∈ ℕ (the paper's ℕ = {1, 2, …}) → p : ℕ with 1 ≤ p; reason: the paper writes ℕ₀ for {0, 1, …}
--   - encoding: ∫_a^b in H′_p and lim_{|Δ|→0} in the H′_p norm → Bochner integral of the continuous H′_p-valued map (through the isometry of H′_p onto ℓ²) and an ε–δ limit over strictly increasing τ : Fin (n + 1) → ℝ with τ 0 = a, τ n = b and all steps < δ; reason: the Riemann integral of a continuous Hilbert-space-valued function is its Bochner integral; the mesh limit is this ε–δ statement
--   - reading: the limit in H′_p → also asserts that the Riemann sums lie in H′_p; reason: implicit in the page; excludes a junk value
--   - reading: t ↦ Y(t)♦W_σ(t) is H′_p-valued → H′_p-valued and continuous from [a, b] into H′_p; reason: STEP 2 of the page's proof (p.25), which the page uses to read ∫_a^b Y♦W_σ dt as the Riemann integral of a continuous Hilbert-space-valued function; a stronger conclusion
--   - encoding: the interval [a, b] with partitions a = t₀ < ⋯ < t_n = b → hypothesis a < b; reason: a partition with t₀ < t_n exists only when a < b; the degenerate a = b has no partitions
-- source:
--   Alpay, Jorgensen, Levanony, A class of Gaussian processes with fractional spectral measures, arXiv:1009.0233v1, Theorem 7.1, pp.24–25

import Mathlib
import Definitions.Def_FractionalSpectralGP_SpectralSetting
import Definitions.Def_FractionalSpectralGP_IsRealHilbertBasis
import Definitions.Def_FractionalSpectralGP_Omega
import Definitions.Def_FractionalSpectralGP_IsWhiteNoise
import Definitions.Def_FractionalSpectralGP_IsWienerIsometry
import Definitions.Def_FractionalSpectralGP_chaosCoeff
import Definitions.Def_FractionalSpectralGP_MemHprime
import Definitions.Def_FractionalSpectralGP_embedHprime
import Definitions.Def_FractionalSpectralGP_MemSminus1
import Definitions.Def_FractionalSpectralGP_IsStronglyContinuousOn
import Definitions.Def_FractionalSpectralGP_wick
import Definitions.Def_FractionalSpectralGP_Xsigma
import Definitions.Def_FractionalSpectralGP_Wsigma

open MeasureTheory Complex Filter Topology ProbabilityTheory
open scoped SchwartzMap ENNReal

namespace FractionalSpectralGP

/-- Theorem 7.1 (Alpay, Jorgensen, Levanony, arXiv:1009.0233v1, pp.24–25): let `Y(t)`, `t ∈ [a, b]`, be an `S_{−1}`-valued
function, continuous in the strong topology of `S_{−1}`. Then there exists `p ∈ ℕ` such that the
function `t ↦ Y(t) ♦ W_σ(t)` is `𝓗'_p`-valued, and
`∫_a^b Y(t) ♦ W_σ(t) dt = lim_{|Δ|→0} Σ_{k=0}^{n−1} Y(t_k) ♦ (X_σ(t_{k+1}) − X_σ(t_k))`,
the limit in the `𝓗'_p` norm, over partitions `Δ : a = t₀ < ⋯ < t_n = b` with mesh
`|Δ| = max_k (t_{k+1} − t_k)`.

**Formalization Note.** One `p ≥ 1` serves every clause and every partition. The map
`t ↦ Y(t) ♦ W_σ(t)` is asserted continuous into `𝓗'_p`, so its integral is the integral of a
continuous Hilbert-space-valued function (p.25), never a junk `0`; the Riemann sums are asserted to
lie in `𝓗'_p`. `X_σ`, `W_σ` are the paper's constructions from `σ`, `(λ_n)`, the real basis
`(h_n)`, the white noise `P` (4.1) and the isometry `f ↦ f̃` (4.2); `W_σ(t)` and the increments of
`X_σ` enter `S_{−1}` through their chaos coefficients. -/
theorem wick_ito_integral_eq_lim_riemann_sums (S : SpectralSetting) (h : HilbertBasis ℕ ℂ (Lp ℂ 2 (volume : Measure ℝ)))
    (hh : IsRealHilbertBasis h) (P : Measure Omega) (hP : IsWhiteNoise P)
    (ι : Lp ℂ 2 (volume : Measure ℝ) →ₗᵢ[ℂ] Lp ℂ 2 P) (hι : IsWienerIsometry P ι) (a b : ℝ) (hab : a < b)
    (Y : ℝ → (ℕ →₀ ℕ) → ℂ) (hY : ∀ t ∈ Set.Icc a b, MemSminus1 (Y t))
    (hYc : IsStronglyContinuousOn Y a b) :
    ∃ p : ℕ, 1 ≤ p ∧
      (∀ t ∈ Set.Icc a b, MemHprime p (wick (Y t) (chaosCoeff P ι h (Wsigma S h P ι t)))) ∧
      ContinuousOn (fun t => embedHprime p (wick (Y t) (chaosCoeff P ι h (Wsigma S h P ι t))))
        (Set.Icc a b) ∧
      ∀ ε > 0, ∃ δ > 0, ∀ (n : ℕ) (τ : Fin (n + 1) → ℝ), StrictMono τ → τ 0 = a →
        τ (Fin.last n) = b → (∀ k : Fin n, τ k.succ - τ k.castSucc < δ) →
        MemHprime p (∑ k : Fin n, wick (Y (τ k.castSucc))
            (chaosCoeff P ι h (Xsigma S h P ι (τ k.succ) - Xsigma S h P ι (τ k.castSucc)))) ∧
        ‖(∫ t in a..b, embedHprime p (wick (Y t) (chaosCoeff P ι h (Wsigma S h P ι t)))) -
            embedHprime p (∑ k : Fin n, wick (Y (τ k.castSucc))
              (chaosCoeff P ι h (Xsigma S h P ι (τ k.succ) - Xsigma S h P ι (τ k.castSucc))))‖
          < ε := by sorry

end FractionalSpectralGP
