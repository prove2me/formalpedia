-- Prove2me | Theorems.Thm_GaussDiffSVP_proposition_4_4
-- name    : GaussDiffSVP.proposition_4_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T22:02:22.348854+00:00
-- url     : https://prove2.me/theorems/359bf84c-a23c-4c46-a759-f2de49848d47
-- title:
--   Proposition 4.4 — isolated pairing: $(e^{-D}-e^D\theta)\lambda\le m_{\mathrm{iso}}\le e^D\lambda$, $S_{\mathrm{iso}}\le e^D\lambda^{\otimes2}$
-- statement:
--   Let the input lists be independent and satisfy $\mathcal C(\nu_L,\varepsilon_L)$, $\mathcal C(\nu_R,\varepsilon_R)$; set $D = \varepsilon_L+\varepsilon_R$. Activate pairs with probability $q = cK\le1$ by pairwise independent coins and keep only isolated edges. Put
--   $$\lambda = \Phi_q(\nu_L,\nu_R),\quad D^+ = \sup_x\sum_yK(x,y)\nu_R(y),\quad D^- = \sup_y\sum_xK(x,y)\nu_L(x),\quad\theta = c(D^++D^-).$$
--   Then
--   $$(e^{-D}-e^{D}\theta)\lambda\le m_{\mathrm{iso}}\le e^{D}\lambda,\qquad S^{\mathrm{act}}_{\mathrm{iso}}\le e^{D}\lambda^{\otimes2}.$$
--   Isolation removes the shared-endpoint terms of (23), at the price of the loss $\theta$; this is what lets the error pass through many cooling rounds.
--
--   Differences from the source:
--   - encoding: $(e^{-D}-e^D\theta)\lambda\le m_{\mathrm{iso}}$ → $e^{-D}\lambda\le m_{\mathrm{iso}}+e^D\theta\lambda$; reason: equivalent for finite $\lambda$; avoids truncated subtraction in $[0,\infty]$
--   - encoding: $c$, $K$, suprema, moments → values in $[0,\infty]$; conditional laws given the fixed information; reason: same instances
-- source:
--   Gao–Han–Hu, Gaussian Difference Dynamics: Breaking the 2^{n/2} Barrier for the Shortest Vector Problem and Discrete Gaussian Sampling, arXiv:2611.04336 (held version, sha256 233bf8bb…0692), Proposition 4.4, p.25

import Mathlib
import Definitions.Def_GaussDiffSVP_InClassC
import Definitions.Def_GaussDiffSVP_transport1
import Definitions.Def_GaussDiffSVP_IsCoinKernel
import Definitions.Def_GaussDiffSVP_isoMergeLaw

open scoped ENNReal

namespace GaussDiffSVP

/-- Proposition 4.4 (Gao–Han–Hu, *Gaussian Difference Dynamics*, arXiv:2611.04336 (held version, sha256 233bf8bb…0692), p.25). The input lists are independent and satisfy the factorial moment
bounds `C(ν_L, ε_L)`, `C(ν_R, ε_R)`; set `D = ε_L + ε_R`. Pairs are activated with probability
`q = cK ≤ 1` by pairwise independent coins, and only isolated edges are kept. Put
`λ = Φ_q(ν_L, ν_R)`, `D⁺ = sup_x ∑_y K(x, y)ν_R(y)`, `D⁻ = sup_y ∑_x K(x, y)ν_L(x)` and
`θ = c(D⁺ + D⁻)`. Then `(e^{−D} − e^{D}θ)λ ≤ m_iso ≤ e^{D}λ` (31) and `S_iso^{act} ≤ e^{D}λ^{⊗2}` (32).

**Formalization Note.** The moments are conditional on the fixed information (the laws are the
conditional laws). `c`, `K`, the suprema and all moments are in `ℝ≥0∞`. The lower bound of (31) is
written additively, `e^{−D}λ ≤ m_iso + e^{D}θλ`, which is (31) whenever `λ` is finite and avoids
truncated subtraction in `ℝ≥0∞`. -/
theorem proposition_4_4 {α β γ : Type*} (μL : PMF (List α)) (μR : PMF (List β))
    (T : α → β → γ) (c : ℝ≥0∞) (K : α → β → ℝ≥0∞) (hq : ∀ x y, c * K x y ≤ 1)
    (κ : (lL : List α) → (lR : List β) → PMF (Fin lL.length × Fin lR.length → Bool))
    (hκ : IsCoinKernel (fun x y => c * K x y) κ)
    (νL : α → ℝ≥0∞) (νR : β → ℝ≥0∞) (εL εR : ℝ)
    (hL : InClassC μL νL εL) (hR : InClassC μR νR εR) :
    let D := εL + εR
    let lam := transport1 T (fun x y => c * K x y) νL νR
    let θ := c * ((⨆ x, ∑' y, K x y * νR y) + (⨆ y, ∑' x, K x y * νL x))
    (∀ z, ENNReal.ofReal (Real.exp (-D)) * lam z ≤
        intensity (isoMergeLaw μL μR T κ) z + ENNReal.ofReal (Real.exp D) * θ * lam z) ∧
      (∀ z, intensity (isoMergeLaw μL μR T κ) z ≤ ENNReal.ofReal (Real.exp D) * lam z) ∧
      ∀ z z', factMoment (isoMergeLaw μL μR T κ) z z' ≤
        ENNReal.ofReal (Real.exp D) * (lam z * lam z') := by sorry

end GaussDiffSVP
