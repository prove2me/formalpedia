-- Prove2me | Theorems.Thm_OAI_Problem346_span_purePowers_eq_top
-- name    : OAI.Problem346.span_purePowers_eq_top
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T16:54:31.071979+00:00
-- url     : https://prove2.me/theorems/1f1338ce-e10f-436d-8f83-31aa53c782c7
-- title:
--   Pure powers $v^b$ span the symmetric power $\mathrm{Sym}^bV$
-- statement:
--   Let $V$ be a complex vector space (of arbitrary dimension) and let $b\in\mathbb{N}$. Inside the symmetric algebra of $V$, let $\mathrm{Sym}^bV$ be the linear span of all products $v_1v_2\cdots v_b$ with $v_1,\dots,v_b\in V$. For $v\in V$ the *pure power* $v^b=v\cdots v$ ($b$ factors) is such a product.
--
--   **Theorem.** The pure powers span $\mathrm{Sym}^bV$:
--
--   $$\operatorname{span}_{\mathbb{C}}\{\,v^b : v\in V\,\}=\mathrm{Sym}^bV .$$
--
--   This includes $b=0$, where $\mathrm{Sym}^0V=\mathbb{C}\cdot1$ and $v^0=1$.
--
--   Every element of $\mathrm{Sym}^bV$ is therefore a finite linear combination of $b$-th powers of vectors. Consequently a linear map out of $\mathrm{Sym}^bV$ is determined by its values on pure powers, which reduces identities on symmetric powers to the diagonal case $v_1=\dots=v_b$.
--
--   **Formalization Note** $\mathrm{Sym}^bV$ is `SymPow b V`, a submodule of `SymmetricAlgebra ℂ V` regarded as a type, and $v^b$ is `symMonomial b V (fun _ => v)`; the statement says that the span of the range of this map is `⊤` in `SymPow b V`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/RepresentationTheory/FoulkesHowe/PowerSpan.lean#L13-L32

import Mathlib
import Definitions.Def_FoulkesHowe
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_Model
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_DegreeOne
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_Functoriality
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_LinearCase
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_PermanentPairing
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_SymmetricLift
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_AlgebraEvaluation
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_SymmetricDual
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_TensorPresentation
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_FiniteDimension
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_MonomialMultilinear
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_Spanning
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_Actions
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_Naturality
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_DualEmbedding
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_PairingConstruction
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_FoulkesMultilinear
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_CanonicalMap
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_Multiplication
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_VanishingInduction
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_DiagonalCoefficient
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_FirstLabels
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_FlattenedForm
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_MultilinearPolynomial
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_BlockWeight
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_FirstPolynomial
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_PolynomialShift
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_FirstCounts
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_SlotDerivative
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_TransferEndpoints

open OAI OAI.Problem346
universe u v

theorem OAI.Problem346.span_purePowers_eq_top (b : ℕ) (V : Type u)
    [AddCommGroup V] [Module ℂ V] :
    Submodule.span ℂ (Set.range (fun x : V => symMonomial b V (fun _ => x))) = ⊤ := by sorry
