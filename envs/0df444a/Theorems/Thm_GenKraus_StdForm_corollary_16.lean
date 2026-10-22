-- Prove2me | Theorems.Thm_GenKraus_StdForm_corollary_16
-- name    : GenKraus.StdForm.corollary_16
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:24:04.377048+00:00
-- url     : https://prove2.me/theorems/83b95ed6-5edd-4f12-8ad4-a6948111ebc4
-- title:
--   Corollary 16, p. 18 — if 𝒬 maps 𝒟²_e into ℬ(ℋ), the generalized Kraus operators map 𝒟_e into ℋ
-- statement:
--   Let $\{e_n\},\{f_n\}$, $\mathcal D_e,\mathcal D_f,\mathcal D_e^2$, $E_{k\ell}$ and the completely positive form-valued map $Q$ be as in Theorem 14. Assume moreover that each form $Q(\rho)$, $\rho\in\mathcal D_e^2$, is given by a bounded operator $\breve Q(\rho)\in\mathcal B(\mathcal H)$: $\langle g|Q(\rho)|h\rangle=\langle g|\breve Q(\rho)h\rangle$ for all $g,h\in\mathcal D_f$.
--
--   Let $(K_\alpha)$ be any countable family of generalized Kraus operators representing $Q$, i.e. $\langle g|Q(E_{k\ell})|h\rangle=\sum_\alpha\langle g|K_\alpha|e_k\rangle\overline{\langle h|K_\alpha|e_\ell\rangle}$ for all $k,\ell$ and $g,h\in\mathcal D_f$. Then each $K_\alpha$ maps $\mathcal D_e$ into $\mathcal H$: for every $\alpha$ and every $\varphi\in\mathcal D_e$ there is a vector $w\in\mathcal H$ with
--
--   $$\langle g|K_\alpha|\varphi\rangle=\langle g|w\rangle\qquad\text{for all } g\in\mathcal D_f .$$
--
--   This is what makes the Kraus operators $L_k$ of the generalized standard form genuine operators $\mathcal D_e\to\mathcal H$ when $Q=\mathcal L_+$, whose values are trace-class.
--
--   **Formalization Note** The conclusion is stated for every representing family, as the proof on p. 18 works for any family satisfying (23). $w$ is the vector $K_\alpha\varphi$; the matrix elements are conjugate-linear in $g$, as is $\langle g|w\rangle$.
-- source:
--   Alazzawi–Baumgartner, Generalized Kraus Operators and Generators of Quantum Dynamical Semigroups, arXiv:1306.4531v4, p. 18, Corollary 16 (= second sentence of Theorem 14, p. 15)

import Mathlib
import Definitions.Def_GenKraus_StdForm_Setting
open Filter Topology
open QAlgorithms.Papers.Independent.Dependency50.P13 (TraceClass traceNormValue operatorTrace)
open QAlgorithms.Papers.Independent.Next46.P09 (TraceDynamicalSemigroup InTraceGeneratorGraph TraceGeneratorDomain)
open QAlgorithms.Papers.Independent.Claimed50.P50 (ContractionSemigroup)

namespace GenKraus.StdForm

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {I : Type*} {b : HilbertBasis I ℂ H}

/-- Corollary 16, p. 18 (= second sentence of Theorem 14): if every form Q(ρ) is given on 𝒟_f by
a bounded operator Q̆(ρ), then every family of generalized Kraus operators K_α satisfying (23)
maps 𝒟_e into ℋ: each K_α φ is a vector w with ⟨g|K_α|φ⟩ = ⟨g, w⟩ for g ∈ 𝒟_f. -/
theorem corollary_16 (e f : HilbertBasis ℕ ℂ H) (Q : matrixUnits (Set.range e) →ₗ[ℂ] FormOn f)
    (hQ : IsFormCP e f Q)
    (hB : ∀ ρ, ∃ B : H →L[ℂ] H, ∀ g h : Submodule.span ℂ (Set.range f),
      Q ρ g h = inner ℂ (g : H) (B h))
    {A : Type} [Countable A]
    (K : A → Submodule.span ℂ (Set.range e) →ₗ[ℂ] (Submodule.span ℂ (Set.range f) →ₗ⋆[ℂ] ℂ))
    (hK : ∀ (k l : ℕ) (g h : Submodule.span ℂ (Set.range f)),
        HasSum (fun α => K α ⟨e k, Submodule.subset_span ⟨k, rfl⟩⟩ g *
            starRingEnd ℂ (K α ⟨e l, Submodule.subset_span ⟨l, rfl⟩⟩ h))
          (Q (matrixUnit e k l) g h)) :
    ∀ (α : A) (φ : Submodule.span ℂ (Set.range e)), ∃ w : H,
      ∀ g : Submodule.span ℂ (Set.range f), K α φ g = inner ℂ (g : H) w := by sorry

end GenKraus.StdForm
