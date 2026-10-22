-- Prove2me | Theorems.Thm_GelfandVNA_Duality_proposition_5_16
-- name    : GelfandVNA.Duality.proposition_5_16
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T13:49:27.739327+00:00
-- url     : https://prove2.me/theorems/5bf855de-588d-4ddd-b542-b7a080844693
-- title:
--   Proposition 5.16, p. 43 — every (X, M, N) in CSLEMS is isomorphic to Spec(ML(X, M, N))
-- statement:
--   For every compact strictly localizable enhanced measurable space $(X,M,N)$ there is an isomorphism in EMS
--   $$\eta_{(X,M,N)}\colon(X,M,N)\ \xrightarrow{\ \sim\ }\ \mathrm{Spec}(\mathsf{ML}(X,M,N)),$$
--   where $\mathrm{Spec}(\mathsf{ML}(X,M,N))=\mathrm{TM}(\mathrm{Sp}(\mathrm{Ideal}(M/N)))$ is the Stone spectrum of the Boolean algebra $M/N$ with its σ-ideal of meager sets and σ-algebra of Baire sets.
--
--   This is the technical heart of the paper: $\eta$ comes from the von Neumann–Maharam lifting theorem (strict localizability) and its inverse $\psi$ from compactness. It is the unit of the equivalence of Theorem 5.19.
--
--   **Formalization Note** $M/N$ is replaced by a complete Boolean algebra $B$ order-isomorphic to it, whose Stone spectrum is homeomorphic to that of $M/N$. Since CSLEMS is a full subcategory of EMS, an isomorphism in EMS is an isomorphism in CSLEMS. Partial premaps are essential here: if $X\in N$, then $M/N=0$, its spectrum is empty, and $\eta$ has empty domain (Remark 4.9).
-- source:
--   Pavlov, Gelfand-type duality for commutative von Neumann algebras, arXiv:2005.05284v3, p. 43, Proposition 5.16

import Mathlib
import Definitions.Def_GelfandVNA_Duality_EMS

namespace GelfandVNA.Duality

open CategoryTheory

universe u

/-- Proposition 5.16, p. 43: every compact strictly localizable enhanced measurable space
`(X, M, N)` is isomorphic in `EMS` to `Spec(ML(X, M, N)) = TM(Sp(Ideal(M/N)))`, the Stone spectrum of
(a complete Boolean algebra order-isomorphic to) `M/N` with its meager and Baire sets. -/
theorem proposition_5_16 (A : CSLEMS.{u}) :
    ∃ (B : Type u) (_ : CompleteBooleanAlgebra B), Nonempty (MmodN A.obj.E ≃o B) ∧
      Nonempty (A.obj ≅ EMS.of (stoneSpectrum B) (TM (stoneSpectrum B))) := by sorry

end GelfandVNA.Duality
