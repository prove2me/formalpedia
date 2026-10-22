-- Prove2me | Theorems.Thm_NamikiStretch_Lossy_stretching_theorem
-- name    : NamikiStretch.Lossy.stretching_theorem
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T13:48:38.568782+00:00
-- url     : https://prove2.me/theorems/03569680-8504-4d0c-ad27-01c8eb779382
-- title:
--   Theorem, §II.B, p. 4, (26)–(27) (correction sign corrected) — I ⊗ Eη(ρAB) = Λ(I ⊗ Eη/ξ²(ψξ)) for every two-mode density, Λ = CV-Bell projection + displacement
-- statement:
--   Let $\mathcal E_\eta$ be the pure-loss channel with transmissivity $\eta\in(0,1)$, and fix $\xi\in(0,1)$ with $\eta<\xi^2$. Put $\eta'=\eta/\xi^2$. Then $\eta\le\eta'<1$, so $\mathcal E_{\eta'}$ is again a pure-loss channel, and the **effective Choi state**
--   $$\rho_{\mathcal E'}:=\mathcal I\otimes\mathcal E_{\eta'}(\psi_\xi)$$
--   (the two-mode squeezed state $\psi_\xi$ on modes $(A',B)$ with Bob's mode $B$ sent through $\mathcal E_{\eta'}$) simulates $\mathcal E_\eta$ by the following LOCC protocol $\Lambda$. Alice holds a two-mode state $\rho_{RS}$, where $S$ is the mode the channel would carry and $R$ a reference she keeps.
--
--   1. Alice projects $SA'$ onto the CV-Bell state $|\Phi_\beta\rangle$ and announces $\beta=(x+ip)/\sqrt2$.
--   2. Bob applies the displacement $D(\sqrt{\eta'}\,\xi\bar\beta)$ to $B$.
--   3. The output is the average over all outcomes with $dx\,dp$.
--
--   The claim is that for every two-mode density $\rho_{AB}$,
--   $$\mathcal I\otimes\mathcal E_\eta(\rho_{AB})=\Lambda(\rho_{\mathcal E'})=\iint_{\mathbb R^2}\big(\mathbb 1\otimes D(\sqrt{\eta'}\xi\bar\beta)\big)\,\langle\Phi_\beta|_{SA'}\big(\rho_{AB}\otimes\rho_{\mathcal E'}\big)|\Phi_\beta\rangle_{SA'}\,\big(\mathbb 1\otimes D(\sqrt{\eta'}\xi\bar\beta)\big)^\dagger\,dx\,dp .$$
--   Precisely, for all number-basis indices: the series defining $\rho_{\mathcal E'}$, the Bell projection, Bob's displacement conjugation and $\mathcal I\otimes\mathcal E_\eta(\rho_{AB})$ converge absolutely, each entry of the integrand is Lebesgue integrable in $(x,p)$, and its integral equals the corresponding entry of $\mathcal I\otimes\mathcal E_\eta(\rho_{AB})$. The parameters $\eta',\xi$ and the protocol do not depend on $\rho_{AB}$.
--
--   This is the paper's main result: one use of a pure-loss channel, on any input including halves of entangled states, is reproduced exactly by LOCC acting on a finite-energy resource state, which removes the infinite-energy ideal EPR state from the teleportation-stretching argument.
--
--   **Formalization Note** (i) The theorem's "there exist $\eta'\ge\eta$, $\psi_\xi$ and an LOCC process $\Lambda$" is made explicit and uniform: for every admissible $\xi$, with $\eta'=\eta/\xi^2$ as the paper states, and with $\Lambda$ the protocol of (24); this is stronger than the existential. (ii) The hypothesis $\eta<\xi^2$ is the condition that $\eta'<1$ (stated by the paper on p. 5); "state" is the published bipartite density predicate. (iii) Bob's correction is $D(\sqrt{\eta'}\xi\bar\beta)$, not the printed $D^\dagger(\sqrt{\eta'}\xi\beta)$, because of the sign slip in (20) (see milestone (24)). (iv) The CV-Bell projection is the Fock-basis contraction of (16) with (A4); states and outputs are number-basis kernels, the first index being the reference mode.
-- source:
--   Namiki, Teleportation stretching for single-mode Gaussian channels, arXiv:1603.05292v1, p. 4, Theorem, (26)–(27), with the protocol of (24), p. 3; η′ = η/ξ² as stated after (27); ξ² > η as on p. 5

import Mathlib
import Definitions.Def_NamikiStretch_Lossy_Protocol

namespace NamikiStretch.Lossy

open MeasureTheory
open QAlgorithms.Papers.Independent.Dependency50.P39
open QAlgorithms.Papers.Independent.Frontier30.P21

theorem stretching_theorem (η ξ : ℝ) (hη0 : 0 < η) (hη1 : η < 1) (hξ0 : 0 < ξ)
    (hξ1 : ξ < 1) (hηξ : η < ξ ^ 2) (X : BipartiteOperator) (hX : IsBipartiteDensity X) :
    let η' : ℝ := η / ξ ^ 2
    let ρ : ℕ × ℕ → ℕ × ℕ → ℂ := fun p q => X (bipartiteKet q) p
    let ω : ℕ × ℕ → ℕ × ℕ → ℂ := lossOnSecond η' (tmsvKernel ξ)
    let corr : ℝ × ℝ → ℂ := fun z => ((Real.sqrt η' * ξ : ℝ) : ℂ) * star (outcome z)
    let Λρ : ℝ × ℝ → ℕ × ℕ → ℕ × ℕ → ℂ := fun z =>
      dispConjSecond (corr z) (bellBranch ω ρ (outcome z))
    η ≤ η' ∧ η' < 1 ∧
    (∀ p q : ℕ × ℕ,
      Summable (vacuumLossTerm η' (fun m n => tmsvKernel ξ (p.1, m) (q.1, n)) p.2 q.2)) ∧
    (∀ (z : ℝ × ℝ) (p q : ℕ × ℕ), Summable (bellTerm ω ρ (outcome z) p q)) ∧
    (∀ (z : ℝ × ℝ) (p q : ℕ × ℕ), Summable (dispConjTerm (corr z)
        (fun m n => bellBranch ω ρ (outcome z) (p.1, m) (q.1, n)) p.2 q.2)) ∧
    (∀ p q : ℕ × ℕ, Summable (vacuumLossTerm η (fun m n => ρ (p.1, m) (q.1, n)) p.2 q.2)) ∧
    ∀ p q : ℕ × ℕ, Integrable (fun z => Λρ z p q) ∧
      ∫ z : ℝ × ℝ, Λρ z p q = lossOnSecond η ρ p q := by sorry
end NamikiStretch.Lossy
