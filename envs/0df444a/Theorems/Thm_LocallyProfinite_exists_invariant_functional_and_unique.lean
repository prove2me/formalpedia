-- Prove2me | Theorems.Thm_LocallyProfinite_exists_invariant_functional_and_unique
-- name    : LocallyProfinite.exists_invariant_functional_and_unique
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-22T15:31:46.370408+00:00
-- url     : https://prove2.me/theorems/a56ec98f-d0ee-4d9b-871c-efbb3c1baf81
-- title:
--   The left-invariant linear functionals on $C_c^\infty(G)$ of a locally profinite group $G$ form a line
-- statement:
--   **Uniqueness of the invariant functional on $C_c^\infty(G)$ for a locally profinite group** (algebraic form of the existence and uniqueness of Haar measure).
--
--   Let $G$ be a locally profinite group, i.e. a Hausdorff, locally compact, totally disconnected topological group, and let $C_c^\infty(G)$ be the complex vector space of locally constant functions $f\colon G\to\mathbb C$ with compact support. A linear functional $\varphi\colon C_c^\infty(G)\to\mathbb C$ — no continuity or positivity is assumed — is called *left invariant* if
--   $$\varphi\big(x\mapsto f(gx)\big)=\varphi(f)\qquad\text{for all }g\in G,\ f\in C_c^\infty(G).$$
--   Then the space of left-invariant linear functionals on $C_c^\infty(G)$ is one-dimensional: there is a non-zero left-invariant functional $\varphi_0$, and every left-invariant functional $\varphi$ is of the form $\varphi=a\,\varphi_0$ with $a\in\mathbb C$.
--
--   One may take $\varphi_0(f)=\int_Gf\,d\mu$ for a left Haar measure $\mu$; the point of the statement is the uniqueness among *all* linear functionals, with no continuity or positivity assumed. This is the starting point of the theory of smooth representations of $p$-adic groups. The source uses it for $G=F_v^\times$, $v$ a finite place of a number field, in the proof of Proposition B.4.3.1: the Fourier transform of $\log|\cdot|_v$ restricted to $C_c^\infty(F_v^\times)$ is $F_v^\times$-invariant, hence a multiple of $f\mapsto\int_{F_v^\times}f\,d\mu_v$.
--
--   **Formalization Note.** The space $C_c^\infty(G)$ enters as a `Submodule ℂ (G → ℂ)` `V` whose elements are exactly the locally constant functions with compact support (hypothesis `hV`); there is exactly one such submodule, so this is a statement about $C_c^\infty(G)$ itself, and no new definition is needed. Left invariance of `φ : V →ₗ[ℂ] ℂ` is expressed as: whenever `f f' : V` satisfy `f' x = f (g * x)` for all `x`, then `φ f' = φ f` (the translate of an element of `V` is again in `V`). One-dimensionality is expressed by the existence of a non-zero invariant `φ₀` such that every invariant `φ` equals `a • φ₀`.
-- source:
--   A. M. Masullo, The Music of the Primes, draft of 20 November 2026, https://math216.wordpress.com/wp-content/uploads/2026/11/the-music-of-the-primes.pdf, p. 618, proof of Proposition B.4.3.1 (the fact is quoted there with an unresolved citation, printed '[?, Rem. p. 27]')

import Mathlib

open Filter Topology
open scoped Real ContDiff

set_option autoImplicit false

namespace LocallyProfinite

theorem exists_invariant_functional_and_unique
    (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (V : Submodule ℂ (G → ℂ))
    (hV : ∀ f : G → ℂ, f ∈ V ↔ IsLocallyConstant f ∧ HasCompactSupport f) :
    ∃ φ₀ : V →ₗ[ℂ] ℂ, φ₀ ≠ 0 ∧
      (∀ (g : G) (f f' : V), (∀ x : G, (f' : G → ℂ) x = (f : G → ℂ) (g * x)) → φ₀ f' = φ₀ f) ∧
      ∀ φ : V →ₗ[ℂ] ℂ,
        (∀ (g : G) (f f' : V), (∀ x : G, (f' : G → ℂ) x = (f : G → ℂ) (g * x)) → φ f' = φ f) →
        ∃ a : ℂ, φ = a • φ₀ := by sorry

end LocallyProfinite
