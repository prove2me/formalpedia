-- Prove2me | Theorems.Thm_HollandsSanders_CFTBound_lemma_4
-- name    : HollandsSanders.CFTBound.lemma_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T13:45:28.919048+00:00
-- url     : https://prove2.me/theorems/c03d15e5-eca0-43e7-8d7b-bd50e90c77ec
-- title:
--   Lemma 4, p. 48 — a decomposition ω(ab) = Σ φ_j(a)ψ_j(b) with μ = Σ ‖φ_j‖‖ψ_j‖ < ∞ gives a separable σ ⩾ ω with ‖σ‖ = μ
-- statement:
--   Let $\mathfrak A_A,\mathfrak A_B$ be commuting, statistically independent von Neumann algebras on $\mathcal H$ (the standing assumptions of §3), and let $\omega$ be a normal state on $\mathfrak A_A\vee\mathfrak A_B$. Suppose there are (not necessarily positive) normal functionals $\varphi_j$ on $\mathfrak A_A$ and $\psi_j$ on $\mathfrak A_B$ such that
--   $$\omega(ab)=\sum_j\varphi_j(a)\,\psi_j(b)\quad(a\in\mathfrak A_A,\ b\in\mathfrak A_B)\qquad\text{and}\qquad\mu:=\sum_j\|\varphi_j\|\,\|\psi_j\|<\infty.$$
--   Then there is a separable positive linear functional $\sigma$ on $\mathfrak A_A\vee\mathfrak A_B$ with
--   $$\sigma\geqslant\omega\qquad\text{and}\qquad\|\sigma\|=\sigma(1)=\mu.$$
--
--   This is the step that produces a dominating separable functional, hence a bound on the logarithmic dominance $E_N(\omega)\le\ln\mu$.
--
--   **Formalization Note.** Statistical independence ($\mathfrak A_A\vee\mathfrak A_B\cong\mathfrak A_A\otimes\mathfrak A_B$, p. 35) is used in the form that products of positive normal functionals extend to positive normal functionals on the join. $\|\sigma\|=\mu$ is stated as $\sigma(1)=\mu$ in $[0,\infty]$.
-- source:
--   Hollands & Sanders, Entanglement measures and their properties in quantum field theory, arXiv:1702.04924v3, p. 48, Lemma 4 (108), under the standing assumptions of §3 (p. 35)

import Mathlib
import Definitions.Def_BoundedRecovery
import Definitions.Def_HollandsSanders_CFTBound_Entanglement
open OAI.BoundedRecovery
open scoped InnerProductSpace ENNReal

namespace HollandsSanders.CFTBound

/-- Lemma 4 (p. 48). If a normal state `ω` on `𝔄_A ∨ 𝔄_B` decomposes as `ω(ab) = Σⱼ φⱼ(a) ψⱼ(b)`
with normal functionals `φⱼ` on `𝔄_A`, `ψⱼ` on `𝔄_B` and `μ = Σⱼ ‖φⱼ‖ ‖ψⱼ‖ < ∞`, there is a
separable positive functional `σ ⩾ ω` with `‖σ‖ = σ(1) = μ`. Under the standing assumptions of §3
(p. 35): `𝔄_A`, `𝔄_B` commute and are statistically independent. -/
theorem lemma_4 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {AA AB : VonNeumannAlgebra H} (hcomm : AA ≤ AB.commutant) (hind : IsStatIndependent AA AB)
    (ω : (H →L[ℂ] H) → ℂ) (hω : IsNormalState (join AA AB : Set (H →L[ℂ] H)) ω)
    (φ ψ : ℕ → (H →L[ℂ] H) → ℂ)
    (hφ : ∀ j, IsNormalFunctional (AA : Set (H →L[ℂ] H)) (φ j))
    (hψ : ∀ j, IsNormalFunctional (AB : Set (H →L[ℂ] H)) (ψ j))
    (hdec : ∀ a ∈ AA, ∀ b ∈ AB, HasSum (fun j => φ j a * ψ j b) (ω (a * b)))
    (hμ : ∑' j, funcNorm (AA : Set (H →L[ℂ] H)) (φ j) * funcNorm (AB : Set (H →L[ℂ] H)) (ψ j) < ⊤) :
    ∃ σ : (H →L[ℂ] H) → ℂ, IsSeparablePos AA AB σ ∧
      Dominates (join AA AB : Set (H →L[ℂ] H)) σ ω ∧
      ENNReal.ofReal (σ 1).re =
        ∑' j, funcNorm (AA : Set (H →L[ℂ] H)) (φ j) * funcNorm (AB : Set (H →L[ℂ] H)) (ψ j) := by sorry

end HollandsSanders.CFTBound
