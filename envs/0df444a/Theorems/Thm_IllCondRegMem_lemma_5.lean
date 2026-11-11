-- Prove2me | Theorems.Thm_IllCondRegMem_lemma_5
-- name    : IllCondRegMem.lemma_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T09:56:40.145068+00:00
-- url     : https://prove2.me/theorems/19e90422-aaff-4c61-9d0b-3642bc50dec1
-- title:
--   Lemma 5 — masking lemma: $TV(a,b)\le C\frac{d^2\lambda}{\delta_{\max}}\log(ed/\lambda\delta_{\max})^{3/2}+C^{d-p}\delta_{\max}^{d_0-(d-p)/2}\log(ed/\delta_{\max})^{(d-p-d_0)/2}$
-- statement:
--   There is an absolute constant $C>0$ such that the following holds. Fix a subspace $G\subseteq\mathbb R^d$ of dimension $p$, dimensions $d-p\ge d_E\ge d_0\ge(d-p)/2$, and parameters $\lambda\in[0,1/4]$, $\delta_{\max}\in(0,1/4]$. Fix a covariance matrix $\Sigma_G$ on $G$, i.e. $\Sigma_G=P_G\Sigma_GP_G$. Let $E\in\mathrm{Gr}(d_E,d)$ be a random subspace whose distribution is $(d_0,\delta_{\max})$-pruned on $G^\perp$, and let $D_0,D_1$ be random positive semidefinite matrices, arbitrarily correlated with $E$, such that almost surely
--   $$
--   G\subseteq E^\perp,\qquad D_0,D_1\preceq\lambda^2I,\qquad P_GD_0P_G=P_GD_1P_G=\Sigma_G .
--   $$
--   Let $a\sim\mathcal N(0,P_E+D_0)$ and $b\sim\mathcal N(0,P_E+D_1)$ (mixtures over $(E,D_0,D_1)$). Then
--   $$
--   TV(a,b)\le C\,\frac{d^2\lambda}{\delta_{\max}}\log\Big(\frac{ed}{\lambda\delta_{\max}}\Big)^{3/2}+C^{d-p}\,\delta_{\max}^{\,d_0-(d-p)/2}\log\Big(\frac{ed}{\delta_{\max}}\Big)^{(d-p-d_0)/2}.
--   $$
--   Once the posterior on $E$ is pruned on $G^\perp$, an adversary may change the covariance on $(E+G)^\perp$ by up to $\lambda^2$, keeping its compression on $G$ fixed, without the learner noticing. This is the main masking tool of the paper.
--
--   **Formalization Note** $TV$ is the published total variation distance $\sup_A|\mu(A)-\nu(A)|$; $(E,D_0,D_1)$ are measurable random objects on a probability space.
--
--   Differences from the source:
--   - encoding: δ_max ∈ [0, 1/4] → δ_max ∈ (0, 1/4]; reason: the right-hand side of (4) divides by δ_max and is undefined at δ_max = 0
--   - encoding: log(ed/λδ_max) → log(e·d/(λ·δ_max)), whose Lean value makes the first term 0 at λ = 0; reason: at λ = 0 the hypotheses force D₀ = D₁ = 0 and TV(a, b) = 0, as the proof notes
--   - encoding: random subspace E ∈ Gr(d_E, d) and random D₀, D₁ ∈ S^d_+ → measurable random objects; dim E = d_E and positive semidefiniteness required almost surely; reason: random variables are defined up to null sets; same laws
--   - encoding: a ∼ N(0, P_E + D₀), b ∼ N(0, P_E + D₁), TV(a, b) → the Gaussian mixtures over (E, D₀, D₁) and the published tvDist; reason: Lean representation
--   - encoding: constant C → one absolute constant for both terms, chosen before all data; reason: Lean quantifier order
-- source:
--   M. Blanchard, D. Hansen, A. Jayant, V. Sharan, Polynomial Memory-Sample Separations in Non-i.i.d. Ill-Conditioned Regression, STOC 2027 submission (held version, sha256 6369d09f…), Lemma 5, p.8 (PDF pp.9–10); restated p.17 (PDF p.18)

import Mathlib
import Definitions.Def_IllCondRegMem_gaussMixture
import Definitions.Def_IllCondRegMem_IsPrunedOn
import Definitions.Def_FoundationsRL_DECLower_tvDist

open MeasureTheory ProbabilityTheory Matrix

namespace IllCondRegMem

/-- **Lemma 5 (masking lemma).**
Blanchard, Hansen, Jayant, Sharan, *Polynomial Memory-Sample Separations in Non-i.i.d.
Ill-Conditioned Regression*, STOC 2027 submission (held version, sha256 6369d09f…), Lemma 5,
pp.8–9 (restated p.17): "Fix a subspace G ⊆ ℝ^d of dimension p, dimensions
d − p ≥ d_E ≥ d₀ ≥ (d − p)/2, and parameters λ, δ_max ∈ [0, 1/4]. Fix a covariance matrix Σ_G on
G, i.e., Σ_G = P_G Σ_G P_G. Let E ∈ Gr(d_E, d) be a random subspace whose distribution is
(d₀, δ_max)-pruned on G⊥. Let D₀, D₁ ∈ S^d_+ be random PSD matrices that may be arbitrarily
correlated with E. Suppose that almost surely, G ⊆ E⊥, D₀, D₁ ⪯ λ²I, and P_G D₀ P_G = P_G D₁ P_G
= Σ_G. Then, letting a ∼ N(0, P_E + D₀) and b ∼ N(0, P_E + D₁), we have
TV(a, b) ≤ C (d²λ/δ_max) log(ed/λδ_max)^{3/2} + C^{d−p} δ_max^{d₀−(d−p)/2} log(ed/δ_max)^{(d−p−d₀)/2}. (4)"

**Formalization Note.** `C` is one absolute constant for both terms, chosen before all data.
`(E, D₀, D₁)` are measurable random objects on a probability space; `a` and `b` are the mixtures
`E[N(0, P_E + D₀)]`, `E[N(0, P_E + D₁)]` (`gaussMixture`); TV is the published
`FoundationsRL.DECLower.tvDist`. `δ_max ∈ (0, 1/4]`: at `δ_max = 0` the right-hand side of (4) is
undefined. `log(ed/λδ_max)` is `log(e·d/(λ·δ_max))`; at `λ = 0` Lean's value of the first term is
`0`, and then `D₀ = D₁ = 0`. Membership of `E` in `Gr(d_E, d)` and positive semidefiniteness of
`D₀, D₁` are required almost surely. -/
theorem lemma_5 :
    ∃ C : ℝ, 0 < C ∧
      ∀ (d p dE d₀ : ℕ) (G : Submodule ℝ (Vec d)) (lam δmax : ℝ)
        (SG : Matrix (Fin d) (Fin d) ℝ) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
        [IsProbabilityMeasure P] (E : Ω → Submodule ℝ (Vec d))
        (D₀ D₁ : Ω → Matrix (Fin d) (Fin d) ℝ),
        Module.finrank ℝ G = p → dE + p ≤ d → d₀ ≤ dE → ((d : ℝ) - p) / 2 ≤ d₀ →
        0 ≤ lam → lam ≤ 1 / 4 → 0 < δmax → δmax ≤ 1 / 4 →
        projMat G * SG * projMat G = SG →
        IsRandomSubspace E → IsRandomMatrix D₀ → IsRandomMatrix D₁ →
        IsPrunedOn P E G d₀ δmax →
        (∀ᵐ ω ∂P, Module.finrank ℝ (E ω) = dE ∧ (D₀ ω).PosSemidef ∧ (D₁ ω).PosSemidef ∧
          G ≤ (E ω)ᗮ ∧
          (lam ^ 2 • (1 : Matrix (Fin d) (Fin d) ℝ) - D₀ ω).PosSemidef ∧
          (lam ^ 2 • (1 : Matrix (Fin d) (Fin d) ℝ) - D₁ ω).PosSemidef ∧
          projMat G * D₀ ω * projMat G = SG ∧ projMat G * D₁ ω * projMat G = SG) →
        FoundationsRL.DECLower.tvDist
            (gaussMixture P (fun _ => 0) (fun ω => projMat (E ω) + D₀ ω))
            (gaussMixture P (fun _ => 0) (fun ω => projMat (E ω) + D₁ ω)) ≤
          C * ((d : ℝ) ^ 2 * lam / δmax) *
              Real.log (Real.exp 1 * d / (lam * δmax)) ^ ((3 : ℝ) / 2) +
            C ^ (d - p) * δmax ^ ((d₀ : ℝ) - ((d : ℝ) - p) / 2) *
              Real.log (Real.exp 1 * d / δmax) ^ (((d : ℝ) - p - d₀) / 2) := by sorry

end IllCondRegMem
