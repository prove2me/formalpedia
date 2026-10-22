-- Prove2me | Theorems.Thm_NamikiStretch_Lossy_eq_23_coherent
-- name    : NamikiStretch.Lossy.eq_23_coherent
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T13:48:35.561429+00:00
-- url     : https://prove2.me/theorems/7cdbe46f-1ad6-4706-b1ee-1fbf5f4bd20d
-- title:
--   (23), p. 3 (coherent input, corrected) — Eη(Tβ,ξ|α⟩⟨α|T†β,ξ) = ((1−ξ²)/2π) e^{−(1−ξ²)|α−β̄|²} |√ηξ(α−β̄)⟩⟨√ηξ(α−β̄)|
-- statement:
--   Let $\eta,\xi\in(0,1)$, $\alpha,\beta\in\mathbb C$, and let $T_{\beta,\xi}|\alpha\rangle\langle\alpha|T_{\beta,\xi}^\dagger$ be Bob's unnormalized state after Alice projects a coherent input $|\alpha\rangle$ and her half of the two-mode squeezed state $\psi_\xi$ onto the CV-Bell state $|\Phi_\beta\rangle$. Sending it through the pure-loss channel $\mathcal E_\eta$ gives
--   $$\mathcal E_\eta\big(T_{\beta,\xi}|\alpha\rangle\langle\alpha|T_{\beta,\xi}^\dagger\big)=\frac{1-\xi^2}{2\pi}\,e^{-(1-\xi^2)|\alpha-\bar\beta|^2}\,\big|\sqrt\eta\,\xi(\alpha-\bar\beta)\big\rangle\big\langle\sqrt\eta\,\xi(\alpha-\bar\beta)\big| .$$
--   Precisely: the Bell-projection series converge absolutely for all entries, and for all $b,b'\ge0$ the series defining the $(b,b')$ entry of $\mathcal E_\eta(\cdot)$ converges to the $(b,b')$ entry of the right side.
--
--   Equivalently, $\mathcal E_\eta(T_{\beta,\xi}|\alpha\rangle\langle\alpha|T_{\beta,\xi}^\dagger)=D(-\sqrt\eta\xi\bar\beta)\,\mathcal E_{\eta\xi^2}(\tilde\rho_\beta)\,D^\dagger(-\sqrt\eta\xi\bar\beta)$ with $\tilde\rho_\beta=w\,|\alpha\rangle\langle\alpha|$ the coherent-input case of (21) (weight $w$ written with $\alpha-\bar\beta$): the loss after imperfect teleportation acts like a single loss $\eta\xi^2$ up to an outcome-dependent displacement.
--
--   **Formalization Note** (i) *Coherent input*: the paper's derivation uses the $P$ representation (19), which is not a function for nonclassical states; the statement takes $P$ a point mass. (ii) *Corrected sign*: the page has $D(\sqrt\eta\xi\beta)(\mathcal E_{\eta\xi^2}(\tilde\rho_\beta))D^\dagger(\sqrt\eta\xi\beta)$ with $\tilde\rho_\beta$ built from $|\alpha+\beta|^2$, i.e. the output $|\sqrt\eta\xi(\alpha+\beta)\rangle$; this inherits the sign slip of (20). The corrected output has $\alpha-\bar\beta$ (numerically: printed error $0.02$, corrected $10^{-17}$).
-- source:
--   Namiki, Teleportation stretching for single-mode Gaussian channels, arXiv:1603.05292v1, p. 3, (23) (P a point mass; α+β corrected to α−β̄)

import Mathlib
import Definitions.Def_NamikiStretch_Lossy_Protocol

namespace NamikiStretch.Lossy

open MeasureTheory
open QAlgorithms.Papers.Independent.Dependency50.P39
open QAlgorithms.Papers.Independent.Frontier30.P21

theorem eq_23_coherent (η ξ : ℝ) (hη0 : 0 < η) (hη1 : η < 1) (hξ0 : 0 < ξ) (hξ1 : ξ < 1)
    (α β : ℂ) :
    let ρα : Unit × ℕ → Unit × ℕ → ℂ := fun p q => coherentDensity α p.2 q.2
    let w : ℂ := (((1 - ξ ^ 2) / (2 * Real.pi) *
      Real.exp (-(1 - ξ ^ 2) * Complex.normSq (α - star β)) : ℝ) : ℂ)
    (∀ p q : Unit × ℕ, Summable (bellTerm (tmsvKernel ξ) ρα β p q)) ∧
    ∀ b b' : ℕ, HasSum
      (vacuumLossTerm η (fun m n => bellBranch (tmsvKernel ξ) ρα β ((), m) ((), n)) b b')
      (w * coherentDensity (((Real.sqrt η * ξ : ℝ) : ℂ) * (α - star β)) b b') := by sorry
end NamikiStretch.Lossy
