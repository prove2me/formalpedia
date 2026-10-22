-- Prove2me | Theorems.Thm_HollandsSanders_CFTBound_lemma_3
-- name    : HollandsSanders.CFTBound.lemma_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T13:45:30.155047+00:00
-- url     : https://prove2.me/theorems/79d375dc-0f6a-4656-9ee2-227a66125402
-- title:
--   Lemma 3, p. 47 — if ν = ‖Ψ^A‖₁ < ∞, then ω(ab) = Σ φ_j(a)ψ_j(b) with Σ ‖φ_j‖‖ψ_j‖ < ν + ε
-- statement:
--   Let $\mathfrak A_A,\mathfrak A_B$ be commuting von Neumann algebras on $\mathcal H$, and let $\Omega$ be a unit vector that is cyclic and separating for $\mathfrak A_A'$ and for $\mathfrak A_B'$ (the standing assumption of §3.6, footnote 28), with vector state $\omega(x)=\langle\Omega,x\Omega\rangle$. Let $\Psi^A(a)=\Delta^{1/4}a\Omega$ on $\mathfrak A_A$, where $\Delta$ is the modular operator of $\mathfrak A_B'$ and $\Omega$. If
--   $$\nu:=\|\Psi^A\|_1<\infty\quad\text{and}\quad\varepsilon>0,$$
--   there are (not necessarily positive) normal functionals $\varphi_j$ on $\mathfrak A_A$ and $\psi_j$ on $\mathfrak A_B$ with
--   $$\omega(ab)=\sum_j\varphi_j(a)\,\psi_j(b)\quad(a\in\mathfrak A_A,\ b\in\mathfrak A_B)\qquad\text{and}\qquad\sum_j\|\varphi_j\|\,\|\psi_j\|<\nu+\varepsilon.$$
--
--   Together with Lemma 4 this converts a nuclear bound on $\Psi^A$ into a dominating separable functional, which is the content of Theorem 4.
--
--   **Formalization Note.** The standing assumption is encoded by modular data for $\mathfrak A_A'$ and $\mathfrak A_B'$ at $\Omega$; norms are in $[0,\infty]$.
-- source:
--   Hollands & Sanders, Entanglement measures and their properties in quantum field theory, arXiv:1702.04924v3, p. 47, Lemma 3 (107), under the standing assumption of §3.6 (p. 46, footnote 28)

import Mathlib
import Definitions.Def_BoundedRecovery
import Definitions.Def_HollandsSanders_CFTBound_Entanglement
open OAI.BoundedRecovery
open scoped InnerProductSpace ENNReal

namespace HollandsSanders.CFTBound

/-- Lemma 3 (p. 47). Under the standing assumption of §3.6 (footnote 28: the vector `Ω` is cyclic
and separating for `𝔄′_A` and `𝔄′_B`, encoded by the modular data `SA`, `SB` of `𝔄′_A`, `𝔄′_B`
at `Ω`), if `ν = ‖Ψ^A‖₁ < ∞` and `ε > 0`, the vector state `ω` of `Ω` decomposes as
`ω(ab) = Σⱼ φⱼ(a) ψⱼ(b)` with normal functionals `φⱼ` on `𝔄_A`, `ψⱼ` on `𝔄_B` and
`Σⱼ ‖φⱼ‖ ‖ψⱼ‖ < ν + ε`. -/
theorem lemma_3 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {AA AB : VonNeumannAlgebra H} (hcomm : AA ≤ AB.commutant)
    (Om : H) (SA SB : StandardModularData H)
    (hSA : SA.M = AA.commutant) (hSB : SB.M = AB.commutant) (hxA : SA.xi = Om) (hxB : SB.xi = Om)
    (hν : nuclearNorm1 (AA : Set (H →L[ℂ] H)) (quarterMap SB) < ⊤) (ε : ℝ) (hε : 0 < ε) :
    ∃ φ ψ : ℕ → (H →L[ℂ] H) → ℂ,
      (∀ j, IsNormalFunctional (AA : Set (H →L[ℂ] H)) (φ j)) ∧
      (∀ j, IsNormalFunctional (AB : Set (H →L[ℂ] H)) (ψ j)) ∧
      (∀ a ∈ AA, ∀ b ∈ AB, HasSum (fun j => φ j a * ψ j b) (vecState Om (a * b))) ∧
      ∑' j, funcNorm (AA : Set (H →L[ℂ] H)) (φ j) * funcNorm (AB : Set (H →L[ℂ] H)) (ψ j) <
        nuclearNorm1 (AA : Set (H →L[ℂ] H)) (quarterMap SB) + ENNReal.ofReal ε := by sorry

end HollandsSanders.CFTBound
