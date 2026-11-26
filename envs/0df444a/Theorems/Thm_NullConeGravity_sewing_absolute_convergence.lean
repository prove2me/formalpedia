-- Prove2me | Theorems.Thm_NullConeGravity_sewing_absolute_convergence
-- name    : NullConeGravity.sewing_absolute_convergence
-- status  : Open
-- author  : @LG
-- created : 2026-11-26T14:12:19.465814+00:00
-- url     : https://prove2.me/theorems/eda052b4-5ffa-5b41-9d89-d18af4652997
-- title:
--   Absolute convergence of the path-integral composition
-- statement:
--   This is the well-definedness of the Lorentzian path integral under composition across an intermediate cut.
--
--   Let $E$ be a complex Hilbert space, $\{e_i\}_{i\in\iota}$ an orthonormal family with dense span (a Hilbert basis, possibly infinite), and $U_1, U_2 : E \to E$ unitary time-evolution operators. For incoming and outgoing states $\psi,\phi \in E$, the matrix coefficients of the composed evolution satisfy
--
--   $$ \langle \phi, U_2 U_1 \psi\rangle = \sum_{i\in\iota} \langle \phi, U_2 e_i\rangle\,\langle e_i, U_1 \psi\rangle, $$
--
--   and the sum converges **absolutely**, with the bound
--
--   $$ \sum_{i\in\iota} \big|\langle \phi, U_2 e_i\rangle\,\langle e_i, U_1\psi\rangle\big| \le \|\phi\|\,\|\psi\|. $$
--
--   In the source, $E$ is the Hilbert space of states on the intermediate cut $\Sigma$, the $e_i$ are an orthonormal basis of cut states, and $U_1,U_2$ are the unitary evolutions of the two cobordisms being glued. Absolute convergence at finite $G_N$ is what makes the gravitational path integral independent of the subdivision, even when the cut admits infinitely many independent states (gravitons of arbitrarily short wavelength).
--
--   **Formalization Note.** The inner product is conjugate-linear in its first argument. The index type $\iota$ is arbitrary (no `Fintype` assumption), so the statement genuinely covers infinitely many intermediate states; the dense-span hypothesis `htotal` is what turns the orthonormal family into a basis for the reconstruction identity.
-- source:
--   V. Chandrasekaran, An algebraic quantization of gravity from the null cone, https://arxiv.org/abs/2611.34924, Section 4.4, sewing identity and Cauchy–Schwarz bound (labels bfgeo:sewing-main, bfq:sewing-bound)

import Mathlib

namespace NullConeGravity
theorem sewing_absolute_convergence
    {ι : Type*} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (e : ι → E) (he : Orthonormal ℂ e)
    (htotal : (Submodule.span ℂ (Set.range e)).topologicalClosure = ⊤)
    (U₁ U₂ : E ≃ₗᵢ[ℂ] E) (φ ψ : E) :
    Summable (fun i : ι => ‖inner ℂ φ (U₂ (e i)) * inner ℂ (e i) (U₁ ψ)‖) ∧
    (∑' i : ι, inner ℂ φ (U₂ (e i)) * inner ℂ (e i) (U₁ ψ)) = inner ℂ φ (U₂ (U₁ ψ)) ∧
    (∑' i : ι, ‖inner ℂ φ (U₂ (e i)) * inner ℂ (e i) (U₁ ψ)‖) ≤ ‖φ‖ * ‖ψ‖ := by sorry
end NullConeGravity
