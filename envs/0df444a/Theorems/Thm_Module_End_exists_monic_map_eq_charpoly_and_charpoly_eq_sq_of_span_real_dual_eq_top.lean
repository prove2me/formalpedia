-- Prove2me | Theorems.Thm_Module_End_exists_monic_map_eq_charpoly_and_charpoly_eq_sq_of_span_real_dual_eq_top
-- name    : Module.End.exists_monic_map_eq_charpoly_and_charpoly_eq_sq_of_span_real_dual_eq_top
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.335791+00:00
-- url     : https://prove2.me/theorems/46f2ede9-209f-597a-9816-37551479b6ff
-- title:
--   Rational and analytic characteristic polynomials of a complex torus endomorphism
-- statement:
--   Let $S$ be a finite-dimensional complex vector space and let $T\colon S\to S$ be a $\mathbb{C}$-linear endomorphism whose characteristic polynomial is fixed by coefficientwise complex conjugation, i.e. has real coefficients. Let $\Lambda$ be a $\mathbb{Z}$-submodule of the complex dual $\mathrm{Hom}_{\mathbb{C}}(S,\mathbb{C})$ which is finite and free as a $\mathbb{Z}$-module, and let $b\colon \mathrm{Fin}\,n \to \Lambda$ be a $\mathbb{Z}$-basis of $\Lambda$ whose image in $\mathrm{Hom}_{\mathbb{C}}(S,\mathbb{C})$ is linearly independent over $\mathbb{R}$ and spans $\mathrm{Hom}_{\mathbb{C}}(S,\mathbb{C})$ over $\mathbb{R}$; thus $\Lambda$ is a full lattice in the underlying real vector space of the dual. Let $\tau$ be a $\mathbb{Z}$-linear endomorphism of $\Lambda$ which acts as the transpose of $T$, that is, the element of $\mathrm{Hom}_{\mathbb{C}}(S,\mathbb{C})$ underlying $\tau(x)$ equals $x \circ T$ for every $x \in \Lambda$. The conclusion asserts the existence of a monic polynomial $Q \in \mathbb{Z}[X]$ whose image under $\mathbb{Z} \to \mathbb{C}$ is the characteristic polynomial of $T$, and such that the characteristic polynomial of $\tau$ on the free $\mathbb{Z}$-module $\Lambda$ equals $Q^2$.
--
--   This is the comparison between the rational representation of an endomorphism of a complex torus, on the lattice, and its analytic representation, on the (co)tangent space, in the case where the analytic characteristic polynomial is real: in general the rational characteristic polynomial is $\chi_T \cdot \overline{\chi_T}$, which under the reality hypothesis becomes $\chi_T^2$ and in particular forces $\chi_T$ to have integral coefficients. It is used in the construction of the Tate module representation attached to a modular curve, where it identifies the characteristic polynomial of a Hecke operator on the integral homology with the square of an integral polynomial reducing to the analytic one.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Module_End_exists_monic_map_eq_charpoly_and_charpoly_eq_sq_of_span_real_dual_eq_top.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem Module.End.exists_monic_map_eq_charpoly_and_charpoly_eq_sq_of_span_real_dual_eq_top
    {S : Type*} [AddCommGroup S] [Module ℂ S] [FiniteDimensional ℂ S]
    (T : S →ₗ[ℂ] S) (hreal : T.charpoly.map (starRingEnd ℂ) = T.charpoly)
    (Λ : Submodule ℤ (Module.Dual ℂ S)) [Module.Finite ℤ Λ] [Module.Free ℤ Λ]
    {n : ℕ} (b : Module.Basis (Fin n) ℤ Λ)
    (hli : LinearIndependent ℝ (fun i => ((b i : Λ) : Module.Dual ℂ S)))
    (hsp : Submodule.span ℝ (Set.range fun i => ((b i : Λ) : Module.Dual ℂ S)) = ⊤)
    (τ : Module.End ℤ Λ)
    (hτ : ∀ x : Λ, ((τ x : Λ) : Module.Dual ℂ S) = (x : Module.Dual ℂ S) ∘ₗ T) :
    ∃ Q : Polynomial ℤ, Q.Monic ∧ Q.map (algebraMap ℤ ℂ) = T.charpoly ∧ τ.charpoly = Q ^ 2 := by sorry
