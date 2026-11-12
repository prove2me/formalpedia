-- Prove2me | Theorems.Thm_GMMPostSamp_Main_lemma_2
-- name    : GMMPostSamp.Main.lemma_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T06:22:49.726199+00:00
-- url     : https://prove2.me/theorems/c9fef83d-8476-421e-8f64-7a56db5794ab
-- title:
--   Lemma 2 — variance and entropy comparison for mixtures of exponential tilts, with factor 1 + β/λ
-- statement:
--   Let $\mu$ be a probability measure on a standard Borel space $\Omega$, $t:\Omega\to\mathbb R^d$ measurable with $Z_t(v)<\infty$ for all $v$, $\nu$ a probability measure on $\mathbb R^d$, $\pi_v=T_{v,t}\mu$ and $\pi=\int\pi_v\,\nu(dv)$ (12)–(13). Let $\lambda>0$, $\beta\ge0$.
--
--   1. If $\mathrm{Cov}_{\pi_v}[t]\preceq\beta I_d$ for all $v$ and $\mathrm{Var}_\nu[g]\le\frac1\lambda\mathbb E_\nu\|\nabla g\|_2^2$ for all smooth $g$ with $\mathbb E_\nu g^2<\infty$ (14), then every measurable $f$ with $\mathbb E_\pi f^2<\infty$ satisfies
--   $$\mathrm{Var}_\pi[f]\le\Big(1+\frac\beta\lambda\Big)\mathbb E_{v\sim\nu}\big[\mathrm{Var}_{\pi_v}[f]\big].$$
--   2. If $\log\mathbb E_{\pi_v}[e^{\langle u,t-\mathbb E_{\pi_v}t\rangle}]\le\frac\beta2\|u\|_2^2$ for all $u,v$ and $\mathrm{Ent}_\nu[g]\le\frac1{2\lambda}\mathbb E_\nu[\|\nabla g\|_2^2/g]$ for all smooth $g>0$ with $\mathrm{Ent}_\nu[g]<\infty$ (15), then every measurable $f>0$ with $\mathrm{Ent}_\pi[f]<\infty$ satisfies
--   $$\mathrm{Ent}_\pi[f]\le\Big(1+\frac\beta\lambda\Big)\mathbb E_{v\sim\nu}\big[\mathrm{Ent}_{\pi_v}[f]\big].$$
--   This two-scale criterion lifts functional inequalities of the components and the mixing law to the mixture.
--
--   **Formalization Note.** Variances and entropies are $[0,\infty]$-valued, so both sides are meaningful for every $f$; "$\mathrm{Ent}[g]<\infty$" is "$g$ integrable and $\mathrm{Ent}[g]<\infty$"; smooth means $C^\infty$.
--
--   Differences from the source:
--   - reading: setting of (12), (13), Z_t(v) < ∞ for all v; f : Ω → R → t and f measurable; reason: standing measurability convention; the expectations are otherwise undefined
--   - encoding: π = ∫ π_v ν(v) dv → π = κ ∘ ν for a Markov kernel κ with κ v = T_{v,t}µ for every v; reason: the mixture integral needs v ↦ π_v measurable; κ is that map
--   - encoding: Var, Ent, E_ν[‖∇g‖²], E_ν[‖∇g‖²/g] as reals → [0, ∞]-valued (evariance, ent, lintegrals); Ent_ν[g] < ∞ as g integrable and ent finite; reason: avoids junk values of Bochner integrals; same statement where the paper's quantities are finite
--   - encoding: Cov ⪯ βI_d and log E[exp⟨u, t − E t⟩] ≤ (β/2)‖u‖² → quadratic-form and exponentiated forms (CovLe, LogMGFLe); reason: definition of the Loewner order; log increasing
--   - encoding: smooth g → ContDiff ℝ ∞ g; reason: smooth = C^∞
-- source:
--   Kumar, Sarkar, Tian, Zhu, Posterior Sampling in Gaussian Mixture Models Beyond the Clusterability Threshold, STOC 2027 submission (manuscript sha256 ba5079cd…), p. 12, Lemma 2 (adapted from Theorem 3.2 of [Sri26])

import Mathlib
import Definitions.Def_GMMPostSamp_Main_Toolkit

open MeasureTheory ProbabilityTheory

namespace GMMPostSamp.Main

/-- Lemma 2 (p. 12): variance and entropy comparison for the mixture `π = ∫ π_v ν(dv)` of the
tilts `π_v = T_{v,t} µ` (12)–(13), with `λ > 0`, `β ≥ 0` and `Z_t(v) < ∞` for all `v`.
Item 1: under (14), `Var_π[f] ≤ (1 + β/λ) E_{v∼ν}[Var_{π_v}[f]]` for every `f` with
`E_π[f²] < ∞`. Item 2: under (15), `Ent_π[f] ≤ (1 + β/λ) E_{v∼ν}[Ent_{π_v}[f]]` for every
`f > 0` with `Ent_π[f] < ∞`. -/
theorem lemma_2 {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] {d : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (t : Ω → EuclideanSpace ℝ (Fin d))
    (ht : Measurable t) (hZ : ∀ v, Zt μ t v < ⊤)
    (ν : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure ν]
    (κ : Kernel (EuclideanSpace ℝ (Fin d)) Ω) [IsMarkovKernel κ]
    (hκ : ∀ v, κ v = tilt μ t v) (lam β : ℝ) (hlam : 0 < lam) (hβ : 0 ≤ β) :
    (((∀ v, CovLe (κ v) t β) ∧
        ∀ g : EuclideanSpace ℝ (Fin d) → ℝ, ContDiff ℝ (⊤ : ℕ∞) g →
          ∫⁻ v, ‖g v‖ₑ ^ 2 ∂ν < ⊤ →
          evariance g ν ≤ ENNReal.ofReal (1 / lam) * ∫⁻ v, ‖gradient g v‖ₑ ^ 2 ∂ν) →
      ∀ f : Ω → ℝ, Measurable f → ∫⁻ ω, ‖f ω‖ₑ ^ 2 ∂(κ ∘ₘ ν) < ⊤ →
        evariance f (κ ∘ₘ ν) ≤ ENNReal.ofReal (1 + β / lam) * ∫⁻ v, evariance f (κ v) ∂ν) ∧
    (((∀ v, LogMGFLe (κ v) t β) ∧
        ∀ g : EuclideanSpace ℝ (Fin d) → ℝ, ContDiff ℝ (⊤ : ℕ∞) g → (∀ v, 0 < g v) →
          Integrable g ν → ent ν g < ⊤ →
          ent ν g ≤ ENNReal.ofReal (1 / (2 * lam)) *
            ∫⁻ v, ENNReal.ofReal (‖gradient g v‖ ^ 2 / g v) ∂ν) →
      ∀ f : Ω → ℝ, Measurable f → (∀ ω, 0 < f ω) → Integrable f (κ ∘ₘ ν) →
        ent (κ ∘ₘ ν) f < ⊤ →
        ent (κ ∘ₘ ν) f ≤ ENNReal.ofReal (1 + β / lam) * ∫⁻ v, ent (κ v) f ∂ν) := by sorry

end GMMPostSamp.Main
