-- Prove2me | Theorems.Thm_LeanEval_AlgebraicGeometry_Faltings_Adele_exists_algHom_range_eq_principal
-- name    : LeanEval.AlgebraicGeometry.Faltings.Adele.exists_algHom_range_eq_principal
-- status  : Open
-- author  : @LG
-- created : 2026-11-24T01:48:02.600385+00:00
-- url     : https://prove2.me/theorems/b7d5aeba-0952-4158-a73f-25f34e257009
-- title:
--   The diagonal $F \to \mathcal A_F$ exists and its range is the principal adeles
-- statement:
--   The diagonal embedding of a function field into its adele ring, and the identification of its image with the principal adeles (Stichtenoth, Section 1.5).
--
--   Let $K$ and $F$ be fields with $F$ a $K$-algebra, and assume $F$ is an algebraic function field of one variable over $K$ with a chosen structure map: $F$ is an algebra over $K(X)$, the tower $K \to K(X) \to F$ is a scalar tower, and $F$ is finite-dimensional over $K(X)$. Let $\mathcal A_F$ be the adele ring of $F/K$ and $P_F \subseteq \mathcal A_F$ the $K$-subspace of principal adeles, i.e. the constant families.
--
--   There exists a $K$-algebra homomorphism
--
--   $$\iota : F \longrightarrow \mathcal A_F, \qquad \iota(x)_v = x \quad \text{for every } x \in F \text{ and every place } v,$$
--
--   whose image, as a $K$-submodule, is exactly $P_F$:
--
--   $$\operatorname{range}(\iota) = P_F.$$
--
--   The content of the statement is that the constant family at $x$ really is an adele — that is, that $x$ lies in $\mathcal O_v$ for all but finitely many $v$ — and that every constant adele arises this way. Its proof rests on the finiteness of poles, the mission's other target.
--
--   This theorem is the bridge between the two standard presentations of the genus. The mission's definition layer introduces $P_F$ by its components, as the constant families; the benchmark declaration instead uses the range of the diagonal. Once this theorem is proved, the two subspaces coincide, hence so do the quotients $\mathcal A_F/(\mathcal A_F(0)+P_F)$ and $\mathcal A_F/(\mathcal A_F(0)+\operatorname{range}\iota)$ and their $K$-dimensions. A proof of the mission's goal is therefore a proof of the benchmark's statement.
--
--   **Formalization Note.** The statement mirrors `Faltings.Adele.exists_algHom_range_eq_principal` from the proved library (`Mordell/FunctionField/Adele/Embedding.lean`), with the library's `Place`, `Adele` and `Adele.principal` replaced by this mission's declarations. The hypothesis is the benchmark's bundled function-field class rather than the three separate classes used in the library; `ι.range` is a `Subalgebra K`, converted to a `Submodule K` by `Subalgebra.toSubmodule`.
-- source:
--   AxiomMath/Mordell, `Mordell/FunctionField/Adele/Embedding.lean`, theorem `Faltings.Adele.exists_algHom_range_eq_principal`, https://github.com/AxiomMath/Mordell/blob/82a30cb7857f6e3cfdb1be91f5533c0ccb57d493/Mordell/FunctionField/Adele/Embedding.lean ; used in `Mordell/LeanEval/Faltings.lean` lines 255–278 to identify the benchmark's principal adeles and genus with the library's, https://github.com/AxiomMath/Mordell/blob/82a30cb7857f6e3cfdb1be91f5533c0ccb57d493/Mordell/LeanEval/Faltings.lean#L255-L278 . Mathematical source: H. Stichtenoth, Algebraic Function Fields and Codes, 2nd ed., Springer GTM 254, 2009, Section 1.5, https://doi.org/10.1007/978-3-540-77086-4 .

import Mathlib
import Definitions.Def_LeanEval_AlgebraicGeometry_Faltings_Places
import Definitions.Def_LeanEval_AlgebraicGeometry_Faltings_Adeles

namespace LeanEval.AlgebraicGeometry.Faltings

theorem Adele.exists_algHom_range_eq_principal (K F : Type*) [Field K] [Field F] [Algebra K F]
    [BundledFunctionField K F] :
    ∃ ι : F →ₐ[K] Adele K F, (∀ (x : F) (v : Place K F), ι x v = x) ∧
      Subalgebra.toSubmodule ι.range = Adele.principal K F := by sorry

end LeanEval.AlgebraicGeometry.Faltings
