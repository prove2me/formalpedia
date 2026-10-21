-- Prove2me | Theorems.Thm_MarketFreeze_Hetero_proposition_2
-- name    : MarketFreeze.Hetero.proposition_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:32:53.740453+00:00
-- url     : https://prove2.me/theorems/ed14323f-4f9f-489d-acc0-12cfae89291d
-- title:
--   Proposition 2, p. 21 — with trading the unique equilibrium is all-screen on [0, θL], no-screen on [θH, θ̄], heterogeneous with tightness solving (15) on (θL, θH)
-- statement:
--   Assume Assumptions 1–5 with an open interbank market ($\lambda>0$), the intermediate screening-cost condition (A1), the low-boom condition (A3) $\Delta\pi^{hom}(0)>0.5\lambda(X-I)$, and the high-boom condition (A6) $\Delta\pi^{hom}(\bar\theta)<-0.5\lambda(1-\bar\theta)(X-I)-\psi\lambda(X-I)$. Then there are cutoffs $0<\theta_L<\theta_H<\bar\theta$, the unique roots in $[0,\bar\theta]$ of
--   $$-\Delta\pi^{hom}(\theta_L)+0.5\lambda(1-\theta_L)(X-I)=0\ \ \text{(A4)},\qquad \Delta\pi^{hom}(\theta_H)+0.5\lambda(1-\theta_H)(X-I)+\psi\lambda(X-I)=0\ \ \text{(A7)},$$
--   such that:
--   1. for every $\theta\in[0,\theta_L]$ the unique equilibrium is homogeneous: all banks are buyers, raise $E^{hom}(\theta)$ and screen ($s=1$);
--   2. for every $\theta\in[\theta_H,\bar\theta]$ the unique equilibrium is homogeneous: no bank posts equity or screens ($s=0$);
--   3. for every $\theta\in(\theta_L,\theta_H)$ the unique equilibrium is heterogeneous, $0<s<1$, with buyers holding $E^{het}(\theta,n)$ and screening, sellers holding no equity, price $p=X-(X-I)/(1+n)$, and tightness $n=s/(1-s)$ solving
--   $$\lambda(X-I)\left[\frac{1-\theta}{2}\cdot\frac{n-1}{n+1}-\frac{\psi}{(n+1)^2}\right]=\Delta\pi^{hom}(\theta);\qquad(15)$$
--   4. for any larger efficiency $\lambda'\in(\lambda,1]$ under which (A3) and (A6) still hold, the cutoffs $\theta_L',\theta_H'$ defined by (A4) and (A7) at $\lambda'$ satisfy $\theta_L'<\theta_L$ and $\theta_H<\theta_H'$: the heterogeneous region expands on both ends;
--   5. on $(\theta_L,\theta_H)$ the equilibrium tightness $n$ and price $p$ are strictly decreasing in $\theta$.
--
--   This is the main result of the paper: interbank trading makes otherwise identical banks choose different capital structures, and the market freezes (no trading) at both ends of the boom-probability range.
--
--   **Formalization Note** An equilibrium is a buyer share $s\in[0,1]$ satisfying the paper's no-profitable-switch conditions at $s=0,1$ (weak inequalities) and equal buyer and seller profits for $0<s<1$; price and buyer equity are the constructed (13) and (14), not free variables. (A6) is used with the sign required by the sentence before it; the printed sign makes the proposition false. The last sentence of part 2 of the proposition ($|\partial n/\partial\theta|$ and $|\partial p/\partial\theta|$ decrease with $\lambda$) is not stated: the claim about $n$ is false under the proposition's hypotheses, and the claim about $p$ needs derivatives of the implicitly defined equilibrium map. Monotonicity in $\theta$ is stated without derivatives. Assumption 4 is a standing assumption of the paper and is kept. The hypotheses are jointly satisfiable only for small $\lambda$ (about $\lambda\lesssim0.015$ in numerical searches).
-- source:
--   Song & Thakor, Market Freeze and Bank Capital Structure Heterogeneity, SSRN 3667175 (version of 2022-02-21; forthcoming Management Science, doi:10.1287/mnsc.2022.4374), Proposition 2, p. 21; proof, pp. 35–37

import Mathlib
import Definitions.Def_MarketFreeze_Hetero_Model

namespace MarketFreeze.Hetero

theorem proposition_2 (P : Params)
    (h0 : Standing P) (h1 : Assumption1 P) (h2 : Assumption2 P)
    (h3 : Assumption3 P) (h4 : Assumption4 P) (h5 : Assumption5 P)
    (hlam : 0 < P.lam) (hA1 : CondA1 P) (hA3 : CondA3 P)
    (hA6 : CondA6 P) :
    ∃ θL θH : ℝ, 0 < θL ∧ θL < θH ∧ θH < P.θbar ∧
      CondA4 P θL ∧ CondA7 P θH ∧
      (∀ θ ∈ Set.Icc 0 P.θbar, CondA4 P θ → θ = θL) ∧
      (∀ θ ∈ Set.Icc 0 P.θbar, CondA7 P θ → θ = θH) ∧
      (∀ θ ∈ Set.Icc 0 θL, ∀ s : ℝ, IsEquilibrium P θ s ↔ s = 1) ∧
      (∀ θ ∈ Set.Icc θH P.θbar, ∀ s : ℝ, IsEquilibrium P θ s ↔ s = 0) ∧
      (∀ θ ∈ Set.Ioo θL θH,
        ∃ s : ℝ, 0 < s ∧ s < 1 ∧
          (∀ s' : ℝ, IsEquilibrium P θ s' ↔ s' = s) ∧
          eq15LHS P θ (s / (1 - s)) = dPi P θ) ∧
      (∀ lam' θL' θH' : ℝ, P.lam < lam' → lam' ≤ 1 →
        CondA3 { P with lam := lam' } → CondA6 { P with lam := lam' } →
        θL' ∈ Set.Icc 0 P.θbar → CondA4 { P with lam := lam' } θL' →
        θH' ∈ Set.Icc 0 P.θbar → CondA7 { P with lam := lam' } θH' →
        θL' < θL ∧ θH < θH') ∧
      (∀ θ₁ θ₂ s₁ s₂ : ℝ, θL < θ₁ → θ₁ < θ₂ → θ₂ < θH →
        IsEquilibrium P θ₁ s₁ → IsEquilibrium P θ₂ s₂ →
        s₂ / (1 - s₂) < s₁ / (1 - s₁) ∧
          price P (s₂ / (1 - s₂)) < price P (s₁ / (1 - s₁))) := by sorry

end MarketFreeze.Hetero
