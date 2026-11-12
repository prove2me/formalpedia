-- Prove2me | Theorems.Thm_GMMPostSamp_Main_lemma_3
-- name    : GMMPostSamp.Main.lemma_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T06:22:35.494216+00:00
-- url     : https://prove2.me/theorems/fe2d7495-9cea-4460-b09f-4352e53c0626
-- title:
--   Lemma 3 — the Gibbs kernel of a tilt mixture is reversible, with Dirichlet form E_ν[Cov_{π_{s(w)}}[f, g]]
-- statement:
--   Let $\mu$ be a probability measure on a standard Borel space $\Omega$, $t:\Omega\to\mathbb R^d$ measurable with $Z_t(v)<\infty$ for all $v$, $\nu$ a probability measure on $\mathbb R^m$, and $s:\mathbb R^m\to\mathbb R^d$ differentiable on $\mathrm{supp}\,\nu$. Let $\pi_{s(w)}=T_{s(w),t}\mu$ (given as a Markov kernel $\kappa$), $\tilde\pi(w,\omega)=\nu(w)\pi_{s(w)}(\omega)$ (18), and $P$ the Gibbs kernel (19). Then $P$ is reversible with respect to $\pi=\int\pi_{s(w)}\nu(dw)$ and, for all square-integrable $f,g$,
--   $$\mathcal E_P(f,g)=\mathbb E_{w\sim\nu}\big[\mathrm{Cov}_{\pi_{s(w)}}[f,g]\big].$$
--   This identifies the Dirichlet form of the Gibbs sampler with the averaged component covariance, which Proposition 3 combines with Lemma 2.
--
--   **Formalization Note.** Reversibility is Mathlib's `Kernel.IsReversible` (detailed balance on measurable sets); $\pi$ is `κ ∘ₘ ν`.
--
--   Differences from the source:
--   - reading: setting of (13), (18) → t measurable and Z_t(v) < ∞ for every v; reason: the tilts π_{s(w)} are defined only when Z_t is finite; standing assumption of §3.2
--   - encoding: components π_{s(w)} with joint density ν(w)π_{s(w)}(ω) → a Markov kernel κ with κ w = T_{s(w),t}µ for every w; joint law ν ⊗ κ; reason: (18) requires w ↦ π_{s(w)} to be measurable; κ is that map
--   - encoding: w ∼ π̃(· | ω) in (19) → Mathlib's condKernel of the joint law, any version; reason: the conditional is unique up to a null set; reversibility and the Dirichlet form do not depend on the version
--   - reading: E_P(f, g) for functions f, g : Ω → R → f, g square-integrable under π; reason: the Dirichlet form (4) and the PI (5) are used for square-integrable functions, where both sides are finite
-- source:
--   Kumar, Sarkar, Tian, Zhu, Posterior Sampling in Gaussian Mixture Models Beyond the Clusterability Threshold, STOC 2027 submission (manuscript sha256 ba5079cd…), p. 14, Lemma 3

import Mathlib
import Definitions.Def_GMMPostSamp_Main_Toolkit

open MeasureTheory ProbabilityTheory

namespace GMMPostSamp.Main

/-- Lemma 3 (p. 14): in the setting (13), (18) — base measure `µ`, statistic `t`, mixing law
`ν ∈ P(ℝ^m)`, a map `s : ℝ^m → ℝ^d` differentiable on `supp ν`, components
`κ w = π_{s(w)} = T_{s(w),t} µ` — the Gibbs kernel `P` (19) is reversible with respect to
`π = ∫ π_{s(w)} ν(dw)`, and `E_P(f, g) = E_{w∼ν}[Cov_{π_{s(w)}}[f, g]]` for square-integrable
`f, g`. -/
theorem lemma_3 {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] {d m : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (t : Ω → EuclideanSpace ℝ (Fin d))
    (ht : Measurable t) (hZ : ∀ v, Zt μ t v < ⊤)
    (ν : Measure (EuclideanSpace ℝ (Fin m))) [IsProbabilityMeasure ν]
    (s : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin d))
    (hs : ∀ w ∈ ν.support, DifferentiableAt ℝ s w)
    (κ : Kernel (EuclideanSpace ℝ (Fin m)) Ω) [IsMarkovKernel κ]
    (hκ : ∀ w, κ w = tilt μ t (s w)) :
    (gibbsKernel ν κ).IsReversible (κ ∘ₘ ν) ∧
      ∀ f g : Ω → ℝ, MemLp f 2 (κ ∘ₘ ν) → MemLp g 2 (κ ∘ₘ ν) →
        dirichletForm (κ ∘ₘ ν) (gibbsKernel ν κ) f g = ∫ w, cov (κ w) f g ∂ν := by sorry

end GMMPostSamp.Main
