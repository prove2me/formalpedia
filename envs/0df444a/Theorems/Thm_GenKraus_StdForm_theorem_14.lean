-- Prove2me | Theorems.Thm_GenKraus_StdForm_theorem_14
-- name    : GenKraus.StdForm.theorem_14
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:24:11.923187+00:00
-- url     : https://prove2.me/theorems/8b838f8e-220d-49e9-94c3-8323a82e560a
-- title:
--   Theorem 14, p. 15 — a completely positive map from 𝒟²_e into forms on 𝒟_f has countably many generalized Kraus operators
-- statement:
--   Let $\mathcal H$ be an infinite-dimensional complex Hilbert space with two orthonormal bases $\{e_n\}_{n\in\mathbb N}$, $\{f_n\}_{n\in\mathbb N}$, $\mathcal D_e=\operatorname{lin}\{e_n\}$, $\mathcal D_f=\operatorname{lin}\{f_n\}$, and $\mathcal D_e^2=\operatorname{lin}\{E_{k\ell}\}$ with matrix units $E_{k\ell}=|e_k\rangle\langle e_\ell|$. Let $Q$ be a linear map from $\mathcal D_e^2$ into the sesquilinear forms on $\mathcal D_f$ (conjugate-linear in the first argument), completely positive in the sense that $\sum_{a,c}\langle g_a|Q(\rho_{ac})|g_c\rangle\ge0$ for every positive finite block $(\rho_{ac})$ of elements of $\mathcal D_e^2$ and all $g_a\in\mathcal D_f$.
--
--   Then there is a countable family of generalized Kraus operators $K_\alpha$ — linear maps from $\mathcal D_e$ into the conjugate-linear functionals on $\mathcal D_f$, written through their matrix elements $\langle g|K_\alpha|e\rangle$ — such that $Q(\rho)=\sum_\alpha K_\alpha\rho K_\alpha^\dagger$ (23), i.e. for all $k,\ell$ and $g,h\in\mathcal D_f$
--
--   $$\langle g|Q(E_{k\ell})|h\rangle=\sum_\alpha\langle g|K_\alpha|e_k\rangle\,\overline{\langle h|K_\alpha|e_\ell\rangle},$$
--
--   the series converging (unconditionally); here $\overline{\langle h|K_\alpha|e_\ell\rangle}=\langle e_\ell|K_\alpha^\dagger|h\rangle$ by (22).
--
--   The theorem is applied to the expander $\mathcal L_+$ of Proposition 6 to obtain the operators $L_k$ of the generalized standard form.
--
--   **Formalization Note** Indexing both bases by $\mathbb N$ encodes "the Hilbert space of infinite dimension" (Definition 13). The identity is stated on the matrix units $E_{k\ell}$; linearity of both sides gives it on all of $\mathcal D_e^2$. Only the matrix elements of the $K_\alpha$ are encoded, not their realization as maps into algebraic duals. The family is indexed by a countable type, finite allowed.
-- source:
--   Alazzawi–Baumgartner, Generalized Kraus Operators and Generators of Quantum Dynamical Semigroups, arXiv:1306.4531v4, p. 15, Theorem 14 (first sentence), with Definition 13 and Eqs. (22)–(23)

import Mathlib
import Definitions.Def_GenKraus_StdForm_Setting
open Filter Topology
open QAlgorithms.Papers.Independent.Dependency50.P13 (TraceClass traceNormValue operatorTrace)
open QAlgorithms.Papers.Independent.Next46.P09 (TraceDynamicalSemigroup InTraceGeneratorGraph TraceGeneratorDomain)
open QAlgorithms.Papers.Independent.Claimed50.P50 (ContractionSemigroup)

namespace GenKraus.StdForm

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {I : Type*} {b : HilbertBasis I ℂ H}

/-- Theorem 14, p. 15 (first sentence), on the matrix units E_{kℓ} = |e_k⟩⟨e_ℓ|: a completely
positive map Q from 𝒟²_e into forms with common form domain 𝒟_f has countably many generalized
Kraus operators K_α (matrix elements ⟨g|K_α|e⟩, conjugate-linear in g ∈ 𝒟_f) with
⟨g|Q(E_{kℓ})|h⟩ = Σ_α ⟨g|K_α|e_k⟩⟨e_ℓ|K_α†|h⟩. -/
theorem theorem_14 (e f : HilbertBasis ℕ ℂ H) (Q : matrixUnits (Set.range e) →ₗ[ℂ] FormOn f)
    (hQ : IsFormCP e f Q) :
    ∃ (A : Type) (_ : Countable A)
      (K : A → Submodule.span ℂ (Set.range e) →ₗ[ℂ] (Submodule.span ℂ (Set.range f) →ₗ⋆[ℂ] ℂ)),
      ∀ (k l : ℕ) (g h : Submodule.span ℂ (Set.range f)),
        HasSum (fun α => K α ⟨e k, Submodule.subset_span ⟨k, rfl⟩⟩ g *
            starRingEnd ℂ (K α ⟨e l, Submodule.subset_span ⟨l, rfl⟩⟩ h))
          (Q (matrixUnit e k l) g h) := by sorry

end GenKraus.StdForm
