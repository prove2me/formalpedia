-- Prove2me | Theorems.Thm_NamikiStretch_Lossy_eq_24
-- name    : NamikiStretch.Lossy.eq_24
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T13:48:38.178001+00:00
-- url     : https://prove2.me/theorems/6da94312-e6a9-4eec-b588-6d4521ff2d8b
-- title:
--   (24), p. 3 (corrected) — effective teleportation stretching: ∫ D(√ηξβ̄)Eη(Tβ,ξρT†β,ξ)D†(√ηξβ̄) dxdp = Eηξ²(ρ) for every density ρ
-- statement:
--   Let $\eta,\xi\in(0,1)$ and let $\rho$ be any single-mode density operator. For each outcome $\beta=(x+ip)/\sqrt2$, $(x,p)\in\mathbb R^2$, let $T_{\beta,\xi}\rho T_{\beta,\xi}^\dagger=\langle\Phi_\beta|(\rho\otimes|\psi_\xi\rangle\langle\psi_\xi|)|\Phi_\beta\rangle$ be Bob's unnormalized state after Alice's CV-Bell projection, with the two-mode squeezed state $\psi_\xi$ as resource. Then
--   $$\iint_{\mathbb R^2}D(\sqrt\eta\,\xi\bar\beta)\;\mathcal E_\eta\big(T_{\beta,\xi}\rho T_{\beta,\xi}^\dagger\big)\;D^\dagger(\sqrt\eta\,\xi\bar\beta)\;dx\,dp=\mathcal E_{\eta\xi^2}(\rho).$$
--   Precisely, for all $m,n\ge0$: every series defining the Bell projection, the loss channel and the displacement conjugation converges absolutely for every outcome; the $(m,n)$ entry of the integrand is Lebesgue integrable in $(x,p)$; and its integral equals the $(m,n)$ entry of $\mathcal E_{\eta\xi^2}(\rho)$, whose defining series also converges.
--
--   This is the paper's *effective teleportation-stretchable* property of the pure-loss channel: CV-Bell measurement with a finite-squeezing resource, one use of $\mathcal E_\eta$ and an outcome-dependent displacement simulate the channel $\mathcal E_{\eta\xi^2}$ exactly.
--
--   **Formalization Note** (i) *Corrected correction.* The page has the correction $D^\dagger(\sqrt\eta\xi\beta)\,\cdot\,D(\sqrt\eta\xi\beta)$. With the paper's own (4), (16), (A4) and $D(\beta)=e^{\beta a^\dagger-\beta^*a}$ this is false (numerical error $0.38$ for the input $0.6|0\rangle+0.8i|1\rangle$), a consequence of the sign slip in (20); the correction that makes (24) true is conjugation by $D(\sqrt\eta\xi\bar\beta)$, which is what is stated. (ii) The statement is for **every** density, as printed; the paper's derivation via the $P$ representation is not part of the statement. (iii) The integral is over $\mathbb R\times\mathbb R$ with Lebesgue measure, the paper's $dx\,dp$; integrability and summability are conclusions.
-- source:
--   Namiki, Teleportation stretching for single-mode Gaussian channels, arXiv:1603.05292v1, p. 3, (24) (correction D†(√ηξβ)·D(√ηξβ) corrected to D(√ηξβ̄)·D(√ηξβ̄)†)

import Mathlib
import Definitions.Def_NamikiStretch_Lossy_Protocol

namespace NamikiStretch.Lossy

open MeasureTheory
open QAlgorithms.Papers.Independent.Dependency50.P39
open QAlgorithms.Papers.Independent.Frontier30.P21

theorem eq_24 (η ξ : ℝ) (hη0 : 0 < η) (hη1 : η < 1) (hξ0 : 0 < ξ) (hξ1 : ξ < 1)
    (X : FockOperator) (hX : IsDensity X) :
    let K : ℕ → ℕ → ℂ := fun m n => X (fockKet n) m
    let ρ : Unit × ℕ → Unit × ℕ → ℂ := fun p q => K p.2 q.2
    let branch : ℂ → ℕ → ℕ → ℂ := fun β a c => bellBranch (tmsvKernel ξ) ρ β ((), a) ((), c)
    let corr : ℝ × ℝ → ℂ := fun z => ((Real.sqrt η * ξ : ℝ) : ℂ) * star (outcome z)
    let F : ℝ × ℝ → ℕ → ℕ → ℂ := fun z m n =>
      dispConj (corr z) (vacuumLossKernel η (branch (outcome z))) m n
    (∀ (z : ℝ × ℝ) (p q : Unit × ℕ), Summable (bellTerm (tmsvKernel ξ) ρ (outcome z) p q)) ∧
    (∀ (z : ℝ × ℝ) (a b : ℕ), Summable (vacuumLossTerm η (branch (outcome z)) a b)) ∧
    (∀ (z : ℝ × ℝ) (a b : ℕ),
      Summable (dispConjTerm (corr z) (vacuumLossKernel η (branch (outcome z))) a b)) ∧
    (∀ a b : ℕ, Summable (vacuumLossTerm (η * ξ ^ 2) K a b)) ∧
    ∀ m n : ℕ, Integrable (fun z => F z m n) ∧
      ∫ z : ℝ × ℝ, F z m n = vacuumLossKernel (η * ξ ^ 2) K m n := by sorry
end NamikiStretch.Lossy
