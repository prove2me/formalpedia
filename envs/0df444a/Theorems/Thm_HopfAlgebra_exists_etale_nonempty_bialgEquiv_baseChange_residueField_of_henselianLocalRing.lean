-- Prove2me | Theorems.Thm_HopfAlgebra_exists_etale_nonempty_bialgEquiv_baseChange_residueField_of_henselianLocalRing
-- name    : HopfAlgebra.exists_etale_nonempty_bialgEquiv_baseChange_residueField_of_henselianLocalRing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:56.883924+00:00
-- url     : https://prove2.me/theorems/4add574b-811c-5bb4-ac92-3e9f7477213e
-- title:
--   Finite étale Hopf algebras lift over a henselian local ring
-- statement:
--   Let $R$ be a commutative ring which is a henselian local ring, write $k =$ `IsLocalRing.ResidueField R` for its residue field, and let $E_0$ be a commutative ring carrying a Hopf algebra structure over $k$ whose comultiplication is cocommutative, which is finite as a $k$-module and étale as a $k$-algebra. The assertion is that there exist a type $E$ (in the universe $\max(u,v)$), a commutative ring structure on $E$, a Hopf algebra structure on $E$ over $R$ with cocommutative comultiplication, and free and finite module structures witnessing that $E$ is a finite free $R$-module, such that $E$ is étale as an $R$-algebra and such that there exists an isomorphism of $k$-bialgebras $k \otimes_R E \cong E_0$. Thus the lift is simultaneously a lift of the algebra, of the comultiplication and counit (together with the antipode packaged in the Hopf structure), of the cocommutativity, and of finiteness, freeness and étaleness, and the identification of the base change with $E_0$ is asserted only as a nonempty set of bialgebra isomorphisms, with no canonicity claimed.
--
--   In the language of group schemes this is the essential surjectivity half of the equivalence between finite étale commutative group schemes over a henselian local ring $R$ and over its residue field: every such group scheme over $k$ is the special fibre of one over $R$. It is used in the construction, over a henselian base, of the finite étale Hopf algebra through which a given residual object factors, via [`HopfAlgebra.exists_etale_bialgHom_injective_forall_existsUnique_comp_eq_of_henselianLocalRing_of_residueField`](thm.html#HopfAlgebra.exists_etale_bialgHom_injective_forall_existsUnique_comp_eq_of_henselianLocalRing_of_residueField); the underlying algebra is produced by [`Algebra.Etale.exists_free_nonempty_algEquiv_baseChange_residueField_of_isLocalRing`](thm.html#Algebra.Etale.exists_free_nonempty_algEquiv_baseChange_residueField_of_isLocalRing) and the structure maps by the unique-lifting statement [`Algebra.Etale.existsUnique_algHom_baseChange_residueField_eq_of_moduleFinite_of_henselianLocalRing`](thm.html#Algebra.Etale.existsUnique_algHom_baseChange_residueField_eq_of_moduleFinite_of_henselianLocalRing).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HopfAlgebra_exists_etale_nonempty_bialgEquiv_baseChange_residueField_of_henselianLocalRing.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped TensorProduct

universe u v

theorem HopfAlgebra.exists_etale_nonempty_bialgEquiv_baseChange_residueField_of_henselianLocalRing
    (R : Type u) [CommRing R] [HenselianLocalRing R]
    (E₀ : Type v) [CommRing E₀] [HopfAlgebra (IsLocalRing.ResidueField R) E₀]
    [Coalgebra.IsCocomm (IsLocalRing.ResidueField R) E₀] [Module.Finite (IsLocalRing.ResidueField R) E₀]
    [Algebra.Etale (IsLocalRing.ResidueField R) E₀] :
    ∃ (E : Type (max u v)) (_ : CommRing E) (_ : HopfAlgebra R E) (_ : Coalgebra.IsCocomm R E)
      (_ : Module.Free R E) (_ : Module.Finite R E),
      Algebra.Etale R E ∧
      Nonempty (IsLocalRing.ResidueField R ⊗[R] E ≃ₐc[IsLocalRing.ResidueField R] E₀) := by sorry
