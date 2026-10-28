-- Prove2me | Theorems.Thm_NonAbelianDMNRG_Recursion_eq_43
-- name    : NonAbelianDMNRG.Recursion.eq_43
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T09:29:17.289103+00:00
-- url     : https://prove2.me/theorems/a5ade8aa-493c-4973-baac-9194eb8be0ef
-- title:
--   Eq. (43) — Wigner–Eckart theorem for a scalar operator on a space of labelled multiplets
-- statement:
--   Let $G$ be a group and let each label $Q$ carry a unitary representation $\pi_Q$ of $G$ on $\mathbb C^{\dim Q}$. Assume
--   1. every $\pi_Q$ is irreducible (no invariant subspace other than $0$ and the whole space, which is nonzero), and
--   2. representations with distinct labels are inequivalent (no invertible intertwiner between $\pi_Q$ and $\pi_{Q'}$ for $Q\neq Q'$).
--
--   Let $I$ be a finite set of multiplets $i$ with labels $Q_i$, and let $X$ be an operator on the space with basis $|i, Q_i, Q^z_i\rangle$ that is scalar under the block-diagonal symmetry $U(g)=\bigoplus_i \pi_{Q_i}(g)$, i.e. $U(g) X U(g)^\dagger = X$ for all $g$. Then there are numbers $\langle i\Vert X\Vert j\rangle$, the reduced matrix elements, such that
--   $$
--   \langle i, Q_i, Q^z_i \mid X \mid j, Q_j, Q^z_j\rangle = \langle i\Vert X\Vert j\rangle\, \delta_{Q_i,Q_j}\, \delta_{Q^z_i,Q^z_j}.
--   $$
--
--   In the paper this is applied to $R^{[n]}$ in the eigenbasis of $H_n$; it is the reason the reduced density matrix can be stored by one number per pair of multiplets.
--
--   **Formalization Note** When $Q_i = Q_j$ the internal quantum numbers live in the same range $\{0,\dots,\dim Q_i - 1\}$ and are compared by value. Irreducibility is Mathlib's `Representation.IsIrreducible` (simplicity of the lattice of subrepresentations), inequivalence is the emptiness of `Representation.Equiv`. Schur's lemma is not assumed.
-- source:
--   Tóth, Moca, Legeza, Zaránd, Density matrix numerical renormalization group for non-Abelian symmetries, arXiv:0802.4332v1, p. 7, eq. (43)

import Mathlib
import Definitions.Def_WildeQIT_partialTrace
import Definitions.Def_NonAbelianDMNRG_Recursion_Multiplets
open Matrix
open scoped Kronecker

namespace NonAbelianDMNRG.Recursion

/-- **Eq. (43), p. 7 (Wigner–Eckart theorem for a scalar operator).** Let the labels carry
irreducible, pairwise inequivalent unitary representations. On a space of multiplets `i : I` with
labels `Qi i`, an operator `X` invariant under the block-diagonal symmetry transformation is
diagonal in the representation labels and in the internal quantum numbers, with one reduced
matrix element `x i j` per pair of multiplets:
`⟨i, Q_i, Q^z_i | X | j, Q_j, Q^z_j⟩ = ⟨i ‖ X ‖ j⟩ δ_{Q_i, Q_j} δ_{Q^z_i, Q^z_j}`. -/
theorem eq_43 {G : Type} [Group G] {Lab : Type} [DecidableEq Lab] (dim : Lab → ℕ)
    (π : (Q : Lab) → G →* Matrix.unitaryGroup (Fin (dim Q)) ℂ)
    (hirr : ∀ Q : Lab, Representation.IsIrreducible (labelRep dim π Q))
    (hineq : ∀ Q Q' : Lab, Q ≠ Q' →
      IsEmpty (Representation.Equiv (labelRep dim π Q) (labelRep dim π Q')))
    {I : Type} [Fintype I] [DecidableEq I] (Qi : I → Lab)
    (X : Matrix (Multiplets dim Qi) (Multiplets dim Qi) ℂ)
    (hX : ∀ g : G, multipletRep dim π Qi g * X * (multipletRep dim π Qi g)ᴴ = X) :
    ∃ x : I → I → ℂ, ∀ (i j : I) (m : Fin (dim (Qi i))) (m' : Fin (dim (Qi j))),
      X ⟨i, m⟩ ⟨j, m'⟩ = if Qi i = Qi j ∧ m.val = m'.val then x i j else 0 := by sorry

end NonAbelianDMNRG.Recursion
