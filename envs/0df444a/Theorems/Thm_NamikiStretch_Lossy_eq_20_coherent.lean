-- Prove2me | Theorems.Thm_NamikiStretch_Lossy_eq_20_coherent
-- name    : NamikiStretch.Lossy.eq_20_coherent
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T13:48:35.64709+00:00
-- url     : https://prove2.me/theorems/f5dcbee8-1f1b-4a18-af40-0edac3677dbd
-- title:
--   (20), p. 3 (coherent input, corrected) — CV-Bell projection with ψξ leaves Bob ((1−ξ²)/2π) e^{−(1−ξ²)|α−β̄|²} |ξ(α−β̄)⟩⟨ξ(α−β̄)|
-- statement:
--   Let $\xi\in(0,1)$, let $|\psi_\xi\rangle=\sqrt{1-\xi^2}\sum_n\xi^n|n\rangle|n\rangle$ be the two-mode squeezed state on modes $(A',B)$, and let $|\alpha\rangle$ be a coherent state of the input mode $A$. Alice projects $AA'$ onto the CV-Bell state $|\Phi_\beta\rangle=(\mathbb 1\otimes D^\dagger(\beta))|\Phi_0\rangle$. Then Bob's unnormalized conditional state is
--   $$T_{\beta,\xi}\,|\alpha\rangle\langle\alpha|\,T_{\beta,\xi}^\dagger:=\langle\Phi_\beta|\big(|\alpha\rangle\langle\alpha|\otimes|\psi_\xi\rangle\langle\psi_\xi|\big)|\Phi_\beta\rangle=\frac{1-\xi^2}{2\pi}\,e^{-(1-\xi^2)|\alpha-\bar\beta|^2}\,\big|\xi(\alpha-\bar\beta)\big\rangle\big\langle\xi(\alpha-\bar\beta)\big|.$$
--   Precisely: for all $b,b'\ge0$ the four-fold series defining the $(b,b')$ entry of the left side converges absolutely to the $(b,b')$ entry of the right side.
--
--   This is the per-outcome output of finite-squeezing continuous-variable teleportation: a coherent input arrives attenuated by $\xi$ and shifted by the outcome, with a Gaussian outcome weight.
--
--   **Formalization Note** (i) *Coherent input.* The paper states (20) for an arbitrary input written through its Glauber–Sudarshan $P$ function (19). The $P$ function is not a function for nonclassical states, so the formula is stated for a coherent input, i.e. $P$ a point mass at $\alpha$. (ii) *Corrected sign.* The page reads $\langle\alpha^*|D_{A'}(\beta)=\langle\alpha^*+\beta^*|$, which leads to $|\xi(\alpha+\beta)\rangle$ and $e^{-(1-\xi^2)|\alpha+\beta|^2}$. With the paper's own (4), (16), (A4) and $D(\beta)=e^{\beta a^\dagger-\beta^*a}$ one has $\langle\alpha^*|D(\beta)\propto\langle\alpha^*-\beta|$, so the correct formula has $\alpha-\bar\beta$ in place of $\alpha+\beta$; the printed version is off by about $0.02$ numerically, the corrected one agrees to $10^{-17}$. The statement uses the corrected formula. (iii) The Bell projection is the Fock-basis contraction of (16) with (A4); the last line of (20), which also uses $\mathcal E_{\xi^2}(|\alpha\rangle\langle\alpha|)=|\xi\alpha\rangle\langle\xi\alpha|$, is not restated here.
-- source:
--   Namiki, Teleportation stretching for single-mode Gaussian channels, arXiv:1603.05292v1, p. 3, (20) (fifth line; P a point mass; α+β corrected to α−β̄)

import Mathlib
import Definitions.Def_NamikiStretch_Lossy_Protocol

namespace NamikiStretch.Lossy

open MeasureTheory
open QAlgorithms.Papers.Independent.Dependency50.P39
open QAlgorithms.Papers.Independent.Frontier30.P21

theorem eq_20_coherent (ξ : ℝ) (hξ0 : 0 < ξ) (hξ1 : ξ < 1) (α β : ℂ) :
    let ρα : Unit × ℕ → Unit × ℕ → ℂ := fun p q => coherentDensity α p.2 q.2
    let w : ℂ := (((1 - ξ ^ 2) / (2 * Real.pi) *
      Real.exp (-(1 - ξ ^ 2) * Complex.normSq (α - star β)) : ℝ) : ℂ)
    ∀ b b' : ℕ, HasSum (bellTerm (tmsvKernel ξ) ρα β ((), b) ((), b'))
      (w * coherentDensity ((ξ : ℂ) * (α - star β)) b b') := by sorry
end NamikiStretch.Lossy
