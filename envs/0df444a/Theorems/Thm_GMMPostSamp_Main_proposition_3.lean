-- Prove2me | Theorems.Thm_GMMPostSamp_Main_proposition_3
-- name    : GMMPostSamp.Main.proposition_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T06:22:49.137199+00:00
-- url     : https://prove2.me/theorems/af06be64-2c24-44be-b3d5-f47e89fe720c
-- title:
--   Proposition 3 — one Gibbs step contracts χ² and KL by the factor 1 − λ/(λ + βγ²)
-- statement:
--   In the setting of Lemma 3 (base $\mu$, statistic $t$ with $Z_t(v)<\infty$ for all $v$, mixing law $\nu$ on $\mathbb R^m$, map $s$ differentiable on $\mathrm{supp}\,\nu$, components $\pi_{s(w)}$, Gibbs kernel $P$, $\pi=\mathbb E_{w\sim\nu}[\pi_{s(w)}]$), suppose $\|J_s(w)\|_{\mathrm{op}}\le\gamma$ for all $w\in\mathrm{supp}\,\nu$ (20), $\gamma>0$, $\lambda>0$, $\beta\ge0$.
--
--   1. If (14) holds with $d\leftarrow m$ (that is, $\mathrm{Cov}_{\pi_v}[t]\preceq\beta I_d$ for all $v\in\mathbb R^d$ and $\nu$ satisfies the $\lambda$-Poincaré condition on $\mathbb R^m$), then for every probability measure $\rho$ with $\chi^2(\rho\|\pi)<\infty$,
--   $$\chi^2(\rho P\|\pi)\le\Big(1-\frac{\lambda}{\lambda+\beta\gamma^2}\Big)\chi^2(\rho\|\pi).$$
--   2. If (15) holds with $d\leftarrow m$, then for every $\rho$ with $\mathrm{KL}(\rho\|\pi)<\infty$, $\mathrm{KL}(\rho P\|\pi)\le(1-\frac{\lambda}{\lambda+\beta\gamma^2})\mathrm{KL}(\rho\|\pi)$.
--
--   This is the contraction that drives the mixing bound of Corollary 1.
--
--   **Formalization Note.** $\rho P$ is `P ∘ₘ ρ`; $J_s(w)$ is the Fréchet derivative of $s$ with the Euclidean operator norm; $\mathrm{supp}\,\nu$ is Mathlib's `Measure.support`; KL is Mathlib's `klDiv`.
--
--   Differences from the source:
--   - reading: setting of (13), (18), Z_t(v) < ∞ → t measurable; reason: standing measurability convention
--   - encoding: components π_{s(w)}, π = E_{w∼ν}[π_{s(w)}] → Markov kernel κ with κ w = T_{s(w),t}µ; π = κ ∘ ν; reason: (18) needs w ↦ π_{s(w)} measurable
--   - encoding: w ∼ π̃(· | ω) in (19) → Mathlib's condKernel of the joint law; reason: the conditional is unique up to a null set, which does not change ρP
--   - encoding: χ², KL, Var, Ent, E_ν[‖∇g‖²] as reals → [0, ∞]-valued (chiSq is ∞ unless ρ ≪ π; klDiv; evariance; ent; lintegrals); reason: the paper's divergences may be infinite (p. 8)
--   - encoding: ‖J_s(w)‖_op, supp(ν) → ‖fderiv ℝ s w‖ (operator norm, Euclidean norms), Measure.support ν; reason: standard meanings
-- source:
--   Kumar, Sarkar, Tian, Zhu, Posterior Sampling in Gaussian Mixture Models Beyond the Clusterability Threshold, STOC 2027 submission (manuscript sha256 ba5079cd…), pp. 14–15, Proposition 3

import Mathlib
import Definitions.Def_GMMPostSamp_Main_Toolkit

open MeasureTheory ProbabilityTheory

namespace GMMPostSamp.Main

/-- Proposition 3 (pp. 14–15): in the setting (13), (18) with `Z_t(v) < ∞` for all `v` and
`‖J_s(w)‖_op ≤ γ` on `supp ν` (20), the Gibbs kernel `P` (19) contracts χ² under (14) (with
`d ← m`) and KL under (15) (with `d ← m`) towards `π = E_{w∼ν}[π_{s(w)}]` by the factor
`1 − λ/(λ + βγ²)`. -/
theorem proposition_3 {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] {d m : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (t : Ω → EuclideanSpace ℝ (Fin d))
    (ht : Measurable t) (hZ : ∀ v, Zt μ t v < ⊤)
    (ν : Measure (EuclideanSpace ℝ (Fin m))) [IsProbabilityMeasure ν]
    (s : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin d))
    (hs : ∀ w ∈ ν.support, DifferentiableAt ℝ s w)
    (κ : Kernel (EuclideanSpace ℝ (Fin m)) Ω) [IsMarkovKernel κ]
    (hκ : ∀ w, κ w = tilt μ t (s w)) (γ lam β : ℝ) (hγ : 0 < γ)
    (hJ : ∀ w ∈ ν.support, ‖fderiv ℝ s w‖ ≤ γ) (hlam : 0 < lam) (hβ : 0 ≤ β) :
    (((∀ v, CovLe (tilt μ t v) t β) ∧
        ∀ g : EuclideanSpace ℝ (Fin m) → ℝ, ContDiff ℝ (⊤ : ℕ∞) g →
          ∫⁻ w, ‖g w‖ₑ ^ 2 ∂ν < ⊤ →
          evariance g ν ≤ ENNReal.ofReal (1 / lam) * ∫⁻ w, ‖gradient g w‖ₑ ^ 2 ∂ν) →
      ∀ ρ : Measure Ω, IsProbabilityMeasure ρ → chiSq ρ (κ ∘ₘ ν) < ⊤ →
        chiSq (gibbsKernel ν κ ∘ₘ ρ) (κ ∘ₘ ν) ≤
          ENNReal.ofReal (1 - lam / (lam + β * γ ^ 2)) * chiSq ρ (κ ∘ₘ ν)) ∧
    (((∀ v, LogMGFLe (tilt μ t v) t β) ∧
        ∀ g : EuclideanSpace ℝ (Fin m) → ℝ, ContDiff ℝ (⊤ : ℕ∞) g → (∀ w, 0 < g w) →
          Integrable g ν → ent ν g < ⊤ →
          ent ν g ≤ ENNReal.ofReal (1 / (2 * lam)) *
            ∫⁻ w, ENNReal.ofReal (‖gradient g w‖ ^ 2 / g w) ∂ν) →
      ∀ ρ : Measure Ω, IsProbabilityMeasure ρ → InformationTheory.klDiv ρ (κ ∘ₘ ν) < ⊤ →
        InformationTheory.klDiv (gibbsKernel ν κ ∘ₘ ρ) (κ ∘ₘ ν) ≤
          ENNReal.ofReal (1 - lam / (lam + β * γ ^ 2)) *
            InformationTheory.klDiv ρ (κ ∘ₘ ν)) := by sorry

end GMMPostSamp.Main
