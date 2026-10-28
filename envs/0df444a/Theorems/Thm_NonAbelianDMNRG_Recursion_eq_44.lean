-- Prove2me | Theorems.Thm_NonAbelianDMNRG_Recursion_eq_44
-- name    : NonAbelianDMNRG.Recursion.eq_44
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T09:29:09.702869+00:00
-- url     : https://prove2.me/theorems/32c6c759-00bc-412f-8eb0-b830587a12f0
-- title:
--   Eq. (44) with (43) — a scalar $R^{[n]}$ is diagonal in the labels of the canonical basis
-- statement:
--   Assume the setting of the canonical basis (21): labels with unitary representations $\pi_Q$ that are irreducible and pairwise inequivalent, and generalized Clebsch–Gordan matrices that are isometric, intertwining and complete. Let $K$ and $\Lambda$ be finite sets of kept and local multiplets, and let $R$ be an operator on the new space with $U(g) R U(g)^\dagger = R$ for all $g$, where $U(g) = V(g)\otimes L(g)$.
--
--   Then there are numbers $\langle\tilde\imath\Vert\tilde R\Vert\tilde\jmath\rangle$, indexed by pairs of canonical multiplets, such that the matrix elements of $R$ between canonical states are
--   $$
--   \langle \tilde\imath, Q_{\tilde\imath}, Q^z \mid R \mid \tilde\jmath, Q_{\tilde\jmath}, Q^{z\prime}\rangle = \langle\tilde\imath\Vert\tilde R\Vert\tilde\jmath\rangle\, \delta_{Q_{\tilde\imath}, Q_{\tilde\jmath}}\, \delta_{Q^z, Q^{z\prime}} .
--   $$
--
--   The paper obtains the reduced matrix elements in the canonical basis by rotating those in the eigenbasis of $H_n$ with the block-diagonal matrix $\mathcal O^{[n]}$, (44); the content used afterwards is this Wigner–Eckart form in the canonical basis.
--
--   **Formalization Note** The canonical states are the columns of `canonicalBasis`; the bra is the conjugate transpose. Internal quantum numbers of multiplets with equal labels are compared by value. The rotation $\mathcal O^{[n]}$ is not formalized.
-- source:
--   Tóth, Moca, Legeza, Zaránd, Density matrix numerical renormalization group for non-Abelian symmetries, arXiv:0802.4332v1, p. 7, eqs. (43)–(44)

import Mathlib
import Definitions.Def_WildeQIT_partialTrace
import Definitions.Def_NonAbelianDMNRG_Recursion_Multiplets
open Matrix
open scoped Kronecker

namespace NonAbelianDMNRG.Recursion

/-- **Eq. (44) with (43), p. 7 (R in the canonical basis).** With irreducible, pairwise
inequivalent labels and generalized Clebsch–Gordan matrices (isometric, intertwining, complete), an
operator `R` on the new space invariant under `U(g)` is diagonal in the symmetry labels and
internal quantum numbers of the canonical basis (21): there are reduced matrix elements
`r ĩ j̃ = ⟨ĩ ‖ R̃ ‖ j̃⟩` with `⟨ĩ, Q^z | R | j̃, Q^z'⟩ = r ĩ j̃ δ_{Q_ĩ, Q_j̃} δ_{Q^z, Q^z'}`. -/
theorem eq_44 {G : Type} [Group G] {Lab : Type} [DecidableEq Lab] (dim : Lab → ℕ)
    (π : (Q : Lab) → G →* Matrix.unitaryGroup (Fin (dim Q)) ℂ)
    (hirr : ∀ Q : Lab, Representation.IsIrreducible (labelRep dim π Q))
    (hineq : ∀ Q Q' : Lab, Q ≠ Q' →
      IsEmpty (Representation.Equiv (labelRep dim π Q) (labelRep dim π Q')))
    (couple : Lab → Lab → Finset Lab)
    (cg : (q Q Q' : Lab) → Matrix (Fin (dim q) × Fin (dim Q)) (Fin (dim Q')) ℂ)
    (hiso : ∀ q Q : Lab, ∀ Q' ∈ couple q Q, (cg q Q Q')ᴴ * cg q Q Q' = 1)
    (hint : ∀ q Q : Lab, ∀ Q' ∈ couple q Q, ∀ g : G,
      ((π q g : Matrix (Fin (dim q)) (Fin (dim q)) ℂ) ⊗ₖ
          (π Q g : Matrix (Fin (dim Q)) (Fin (dim Q)) ℂ)) * cg q Q Q' =
        cg q Q Q' * (π Q' g : Matrix (Fin (dim Q')) (Fin (dim Q')) ℂ))
    (hcompl : ∀ q Q : Lab, ∑ Q' ∈ couple q Q, cg q Q Q' * (cg q Q Q')ᴴ = 1)
    {K Λ : Type} [Fintype K] [DecidableEq K] [Fintype Λ] [DecidableEq Λ]
    (Qu : K → Lab) (ql : Λ → Lab)
    (R : Matrix (Multiplets dim Qu × Multiplets dim ql) (Multiplets dim Qu × Multiplets dim ql) ℂ)
    (hR : ∀ g : G, newRep dim π Qu ql g * R * (newRep dim π Qu ql g)ᴴ = R) :
    ∃ r : Can couple Qu ql → Can couple Qu ql → ℂ,
      ∀ (i j : Can couple Qu ql) (m : Fin (dim (canLabel couple Qu ql i)))
        (m' : Fin (dim (canLabel couple Qu ql j))),
        ((canonicalBasis dim couple cg Qu ql)ᴴ * R * canonicalBasis dim couple cg Qu ql)
            ⟨i, m⟩ ⟨j, m'⟩ =
          if canLabel couple Qu ql i = canLabel couple Qu ql j ∧ m.val = m'.val then r i j
          else 0 := by sorry

end NonAbelianDMNRG.Recursion
