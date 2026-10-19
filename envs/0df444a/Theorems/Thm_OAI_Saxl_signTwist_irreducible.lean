-- Prove2me | Theorems.Thm_OAI_Saxl_signTwist_irreducible
-- name    : OAI.Saxl.signTwist_irreducible
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T00:22:26.490121+00:00
-- url     : https://prove2.me/theorems/9d63bfc7-a2e5-4d0e-b570-7441e448802f
-- title:
--   Twisting an irreducible representation of $S_n$ by the sign character preserves irreducibility
-- statement:
--   Let $n\in\mathbb{N}$, let $S_n$ be the symmetric group on $\{0,1,\dots,n-1\}$ with sign character $\operatorname{sgn}:S_n\to\{\pm1\}$, and let $\rho$ be a representation of $S_n$ on a complex vector space $V$ (of any dimension). The *sign twist* of $\rho$ is the representation on the same space
--   $$
--   (\operatorname{sgn}\otimes\rho)(g)=\operatorname{sgn}(g)\,\rho(g)\qquad(g\in S_n).
--   $$
--   If $\rho$ is irreducible, that is, $V$ has exactly two $\rho$-invariant linear subspaces, namely $0$ and $V\neq0$, then $\operatorname{sgn}\otimes\rho$ is irreducible as well.
--
--   Together with the irreducibility of Specht modules, this is what allows Schur's lemma to be applied to intertwiners into a sign-twisted Specht module, as in the isomorphism between a Specht module and the sign twist of the Specht module of the transposed shape.
--
--   **Formalization Note** Irreducibility is Mathlib's `Representation.IsIrreducible`, i.e. `IsSimpleOrder` on the lattice of subrepresentations, which includes the requirement $V\neq0$. The sign twist is `signTwist ρ`, defined by `signC g • ρ g` with `signC` the sign as a complex number.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/RepresentationTheory/Saxl/SignEquivalence.lean#L28-L47

import Mathlib
import Definitions.Def_Saxl
import Definitions.Def_OAI_RepresentationTheory_Saxl_Basic
import Definitions.Def_OAI_RepresentationTheory_Saxl_Polytabloid
import Definitions.Def_OAI_RepresentationTheory_Saxl_SpechtSubmodule
import Definitions.Def_OAI_RepresentationTheory_Saxl_SpechtDuality
import Definitions.Def_OAI_RepresentationTheory_Saxl_TableauTransport
import Definitions.Def_OAI_RepresentationTheory_Saxl_StaircaseTensor
import Definitions.Def_OAI_RepresentationTheory_Saxl_HighProjection
import Definitions.Def_OAI_RepresentationTheory_Saxl_CoordinateSector
import Definitions.Def_OAI_RepresentationTheory_Saxl_PositionSplit
import Definitions.Def_OAI_RepresentationTheory_Saxl_BandFactorization
import Definitions.Def_OAI_RepresentationTheory_Saxl_PathAlternation
import Definitions.Def_OAI_RepresentationTheory_Saxl_BandMatrices
import Definitions.Def_OAI_RepresentationTheory_Saxl_PathContraction
import Definitions.Def_OAI_RepresentationTheory_Saxl_ColumnContraction
import Definitions.Def_OAI_RepresentationTheory_Saxl_BandPairing
import Definitions.Def_OAI_RepresentationTheory_Saxl_CyclicSector
import Definitions.Def_OAI_RepresentationTheory_Saxl_BandSupport
import Definitions.Def_OAI_RepresentationTheory_Saxl_ShapeRigidity
import Definitions.Def_OAI_RepresentationTheory_Saxl_SpechtClassification
import Definitions.Def_OAI_RepresentationTheory_Saxl_SupportSeparation
import Definitions.Def_OAI_RepresentationTheory_Saxl_PositionTensor
import Definitions.Def_OAI_RepresentationTheory_Saxl_BandOrbit
import Definitions.Def_OAI_RepresentationTheory_Saxl_BandGlue
import Definitions.Def_OAI_RepresentationTheory_Saxl_SignEquivalence

open OAI OAI.Saxl
open scoped TensorProduct
universe uV

theorem OAI.Saxl.signTwist_irreducible {n : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (Equiv.Perm (Fin n)) V) [Representation.IsIrreducible ρ] :
    Representation.IsIrreducible (signTwist ρ) := by sorry
