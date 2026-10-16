-- Prove2me | Theorems.Thm_OAI_Problem346_multilinearPolynomial_eq_zero_of_replacements
-- name    : OAI.Problem346.multilinearPolynomial_eq_zero_of_replacements
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T16:56:41.817489+00:00
-- url     : https://prove2.me/theorems/3175c1f8-3aa8-4347-8d4c-2ac87b6ba3af
-- title:
--   Cancelling a block shift: a coordinate polynomial vanishes if all single source-to-destination replacements vanish
-- statement:
--   Let $V$ be a complex vector space and let $S$, $I$, $B$ be finite sets: $S$ indexes the *slots* (arguments), $I$ indexes a family of vectors $e\colon I\to V$, and $B$ is a set of *blocks*. Let $L\colon V^S\to\mathbb{C}$ be a multilinear form. For a block assignment $\beta\colon S\to B$ define the coordinate polynomial
--
--   $$P(\beta)=\sum_{k\colon S\to I}L\big((e_{k(s)})_{s\in S}\big)\prod_{s\in S}X_{\beta(s),\,k(s)}\in\mathbb{C}[X_{b,i} : (b,i)\in B\times I],$$
--
--   which is the expansion of $L\big((x_{\beta(s)})_{s\in S}\big)$ after substituting the vector variable $x_b=\sum_iX_{b,i}e_i$ for each block $b$. Write $\beta[s\mapsto d]$ for the assignment that agrees with $\beta$ except that slot $s$ is assigned to block $d$.
--
--   **Theorem.** Let $\mathrm{src}\ne\mathrm{dst}$ be blocks such that fewer slots are assigned to $\mathrm{dst}$ than to $\mathrm{src}$:
--
--   $$\#\{s\in S : \beta(s)=\mathrm{dst}\}<\#\{s\in S : \beta(s)=\mathrm{src}\}.$$
--
--   If $P\big(\beta[s\mapsto\mathrm{dst}]\big)=0$ for every slot $s$ with $\beta(s)=\mathrm{src}$, then $P(\beta)=0$.
--
--   This is a ready-to-use cancellation rule: to prove vanishing for one block assignment, it suffices to prove it for all assignments obtained by moving a single slot from a more populated block to a less populated one. No symmetry of $L$ and no normalizing factorials are needed, and the remaining blocks act as spectators.
--
--   **Formalization Note** $P(\beta)$ is `multilinearPolynomial L e blocks`, $\beta[s\mapsto d]$ is `Function.update blocks s d`, and the two counts are cardinalities of `Finset.univ.filter (fun s => blocks s = b)`. Arbitrary decidable-equality instances on $S$ and $B$ are allowed.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/RepresentationTheory/FoulkesHowe/EncodedCancellation.lean#L13-L52

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
open scoped BigOperators

theorem OAI.Problem346.multilinearPolynomial_eq_zero_of_replacements
    {V S I B : Type*} [AddCommGroup V] [Module ℂ V]
    [Fintype S] [Fintype I] [Fintype B] [hS : DecidableEq S] [hB : DecidableEq B]
    (L : MultilinearMap ℂ (fun _ : S => V) ℂ) (e : I → V)
    (blocks : S → B) (src dst : B) (hsd : src ≠ dst)
    (hdegree : (Finset.univ.filter (fun s => blocks s = dst)).card <
      (Finset.univ.filter (fun s => blocks s = src)).card)
    (hzero : ∀ s, blocks s = src →
      multilinearPolynomial L e (Function.update blocks s dst) = 0) :
    multilinearPolynomial L e blocks = 0 := by sorry
