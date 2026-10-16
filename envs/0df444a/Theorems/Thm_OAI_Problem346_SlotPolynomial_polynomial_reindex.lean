-- Prove2me | Theorems.Thm_OAI_Problem346_SlotPolynomial_polynomial_reindex
-- name    : OAI.Problem346.SlotPolynomial.polynomial_reindex
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T16:44:50.19276+00:00
-- url     : https://prove2.me/theorems/562f39a9-81e2-4253-ae19-93587761d7d2
-- title:
--   Permuting the slot labels of a slot polynomial equals permuting its coefficient array
-- statement:
--   Let $R$ be a commutative ring, let $S$ and $I$ be finite sets and let $B$ be any set. For a coefficient array $c\colon I^S\to R$ (a scalar $c(k)$ for every function $k\colon S\to I$) and a labelling $l\colon S\to B$ of the slots $s\in S$ by blocks, the *slot polynomial* is
--
--   $$P_c(l)=\sum_{k\colon S\to I}c(k)\prod_{s\in S}X_{l(s),\,k(s)}\in R[X_{b,i} : (b,i)\in B\times I].$$
--
--   **Theorem.** For every permutation $e$ of $S$,
--
--   $$P_c(l\circ e)=P_{c^e}(l),\qquad\text{where } c^e(k)=c(k\circ e)\ \text{ for } k\colon S\to I .$$
--
--   Precomposing the labelling with a permutation of the slots can thus be moved onto the coefficient array. In particular, if $c$ is invariant under $e$, that is $c(k\circ e)=c(k)$ for all $k$, then $P_c(l\circ e)=P_c(l)$. This is how symmetries of a multilinear form become identities between slot polynomials with different labellings.
--
--   **Formalization Note** $P_c(l)$ is `SlotPolynomial.polynomial c l` and $e$ is an `Equiv.Perm S`; decidable equality on $S$ is assumed by the surrounding section.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/RepresentationTheory/FoulkesHowe/SlotDerivative.lean#L83-L98

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

open OAI OAI.Problem346 OAI.Problem346.SlotPolynomial
open scoped BigOperators
variable {R A S I B : Type*} [CommRing R] [CommRing A] [Algebra R A] [DecidableEq S]
variable [Fintype S] [Fintype I]

theorem OAI.Problem346.SlotPolynomial.polynomial_reindex (c : (S → I) → R) (l : S → B) (e : Equiv.Perm S) :
    polynomial c (l ∘ e) = polynomial (fun k => c (k ∘ e)) l := by sorry
