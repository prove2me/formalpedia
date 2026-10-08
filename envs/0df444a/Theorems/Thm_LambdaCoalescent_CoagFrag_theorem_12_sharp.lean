-- Prove2me | Theorems.Thm_LambdaCoalescent_CoagFrag_theorem_12_sharp
-- name    : LambdaCoalescent.CoagFrag.theorem_12_sharp
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:22:19.980542+00:00
-- url     : https://prove2.me/theorems/3ed5db16-63d3-48e0-9aa7-3b1a17f8fa0a
-- title:
--   Proof of Theorem 12, p. 1898 — sharper form: for parameters in PAR the coagulation and fragmentation joint laws agree iff (64)
-- statement:
--   Let $\mathrm{PAR}=\{(\alpha,\theta):0\le\alpha<1,\ \theta>-\alpha\}$ and let $(\alpha,\theta)$, $(\alpha_c,\theta_c)$, $(\alpha_1,\theta_1)$, $(\alpha_f,\theta_f)$ lie in PAR. Consider the joint law of $(\Pi,\Pi')$ defined by
--
--   1. $\Pi$ is an $(\alpha,\theta)$ partition and $\Pi'$ is an $(\alpha_c,\theta_c)$-coagulation of $\Pi$,
--
--   and the joint law of $(\Pi,\Pi')$ defined instead by
--
--   2. $\Pi'$ is an $(\alpha_1,\theta_1)$ partition and $\Pi$ is an $(\alpha_f,\theta_f)$-fragmentation of $\Pi'$.
--
--   These two joint laws are identical if and only if the parameters are of the form allowed in Theorem 12, that is
--   $$\alpha_f=\alpha;\qquad \theta_f=-\alpha_1=-\alpha\alpha_c;\qquad \theta_c=\theta/\alpha,\qquad \theta_1=\theta.\tag{64}$$
--
--   The "if" direction is Theorem 12 with $\beta=\alpha_c$; the "only if" direction shows that the parameters of Theorem 12 are the only ones within the two-parameter family for which the coagulation of an $(\alpha,\theta)$ partition is undone by a fragmentation.
--
--   **Formalization Note** The left side quantifies over all probability laws $\mu,\nu,\rho,\kappa$ on $\mathcal P_\infty$ with EPFs $p_{\alpha,\theta}$, $p_{\alpha_c,\theta_c}$, $p_{\alpha_1,\theta_1}$, $p_{\alpha_f,\theta_f}$ (they exist by Lemma 9, so the quantifier is not vacuous) and states equality of the two joint laws exactly as in Theorem 12. In (64) the relation $\theta_c=\theta/\alpha$ is written multiplicatively, $\alpha\theta_c=\theta$, so that no division by $\alpha$ occurs when $\alpha=0$ (allowed by PAR); for $\alpha>0$ the two forms coincide, and for $\alpha=0$ the page's $\theta/\alpha$ is undefined. EPFs are in the cancelled form of the Setting module.
-- source:
--   Pitman, Coalescents with multiple collisions, Ann. Probab. 27 (1999), p. 1898, proof of Theorem 12, definition of PAR and the italicized sharper form with (64)

import Mathlib
import Definitions.Def_LambdaCoalescent_CoagFrag_Setting

namespace LambdaCoalescent.CoagFrag

open MeasureTheory

theorem theorem_12_sharp (α θ αc θc α₁ θ₁ αf θf : ℝ)
    (hα0 : 0 ≤ α) (hα1 : α < 1) (hθ : -α < θ)
    (hαc0 : 0 ≤ αc) (hαc1 : αc < 1) (hθc : -αc < θc)
    (hα₁0 : 0 ≤ α₁) (hα₁1 : α₁ < 1) (hθ₁ : -α₁ < θ₁)
    (hαf0 : 0 ≤ αf) (hαf1 : αf < 1) (hθf : -αf < θf) :
    (∀ (μ ν ρ κ : Measure LambdaCoalescent.Rates.PInf) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
        [IsProbabilityMeasure ρ] [IsProbabilityMeasure κ],
        IsEPFLaw (pdEPF α θ) μ → IsEPFLaw (pdEPF αc θc) ν →
        IsEPFLaw (pdEPF α₁ θ₁) ρ → IsEPFLaw (pdEPF αf θf) κ →
        ∀ S : Set (LambdaCoalescent.Rates.PInf × LambdaCoalescent.Rates.PInf), MeasurableSet S →
          (μ.prod ν) {x | (x.1, coag x.1 x.2) ∈ S} =
            (ρ.prod (Measure.infinitePi (fun _ : ℕ => κ))) {y | (frag y.1 y.2, y.1) ∈ S}) ↔
      (αf = α ∧ θf = -α₁ ∧ α₁ = α * αc ∧ α * θc = θ ∧ θ₁ = θ) := by sorry

end LambdaCoalescent.CoagFrag
