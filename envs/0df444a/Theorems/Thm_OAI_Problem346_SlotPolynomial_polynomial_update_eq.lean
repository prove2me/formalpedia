-- Prove2me | Theorems.Thm_OAI_Problem346_SlotPolynomial_polynomial_update_eq
-- name    : OAI.Problem346.SlotPolynomial.polynomial_update_eq
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T16:46:33.12807+00:00
-- url     : https://prove2.me/theorems/05c5d12e-2a27-4e5f-bc95-2e1902544566
-- title:
--   Relabelling either of two interchangeable, equally labelled slots gives the same slot polynomial
-- statement:
--   Let $R$ be a commutative ring, let $S$ and $I$ be finite sets and let $B$ be any set. For a coefficient array $c\colon I^S\to R$ and a labelling $l\colon S\to B$ of the slots by blocks, the *slot polynomial* is
--
--   $$P_c(l)=\sum_{k\colon S\to I}c(k)\prod_{s\in S}X_{l(s),\,k(s)}\in R[X_{b,i} : (b,i)\in B\times I],$$
--
--   and $l[s\mapsto d]$ denotes the labelling that agrees with $l$ except that slot $s$ receives the label $d$. For $s,t\in S$ let $\tau_{s,t}$ be the transposition of $S$ exchanging $s$ and $t$ (the identity if $s=t$).
--
--   **Theorem.** Let $s,t\in S$ and $d\in B$. Suppose that $l(s)=l(t)$ and that $c$ is invariant under exchanging the slots $s$ and $t$, i.e. $c(k\circ\tau_{s,t})=c(k)$ for every $k\colon S\to I$. Then
--
--   $$P_c\big(l[s\mapsto d]\big)=P_c\big(l[t\mapsto d]\big).$$
--
--   When the derivative of a slot polynomial is expanded as a sum of single-slot replacements, this lemma shows that replacements at interchangeable slots carrying the same label contribute equal terms, so that the sum collapses to a multiple of a single replacement.
--
--   **Formalization Note** $P_c(l)$ is `SlotPolynomial.polynomial c l`, $l[s\mapsto d]$ is `Function.update l s d` and $\tau_{s,t}$ is `Equiv.swap s t`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/RepresentationTheory/FoulkesHowe/SlotDerivative.lean#L109-L126

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

theorem OAI.Problem346.SlotPolynomial.polynomial_update_eq (c : (S → I) → R) (l : S → B) (s t : S) (dst : B)
    (hl : l s = l t)
    (hc : ∀ k, c (k ∘ Equiv.swap s t) = c k) :
    polynomial c (Function.update l s dst) = polynomial c (Function.update l t dst) := by sorry
