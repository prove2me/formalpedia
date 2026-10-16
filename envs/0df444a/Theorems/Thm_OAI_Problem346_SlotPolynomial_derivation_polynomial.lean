-- Prove2me | Theorems.Thm_OAI_Problem346_SlotPolynomial_derivation_polynomial
-- name    : OAI.Problem346.SlotPolynomial.derivation_polynomial
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T16:43:26.699237+00:00
-- url     : https://prove2.me/theorems/cc51e694-4f62-4581-b8b6-c0bd2749afce
-- title:
--   A block shift replaces each source-labelled slot of a slot polynomial in turn
-- statement:
--   Let $R$ be a commutative ring, let $S$ and $I$ be finite sets and let $B$ be any set. Elements of $S$ are *slots*, elements of $B$ are *blocks*, and we work in the polynomial ring $R[X]=R[X_{b,i} : (b,i)\in B\times I]$. Given a coefficient array $c\colon I^S\to R$ (a scalar $c(k)$ for each function $k\colon S\to I$) and a labelling $l\colon S\to B$ of slots by blocks, the *slot polynomial* is
--
--   $$P_c(l)=\sum_{k\colon S\to I}c(k)\prod_{s\in S}X_{l(s),\,k(s)}\in R[X].$$
--
--   For $s\in S$ and $d\in B$ write $l[s\mapsto d]$ for the labelling that agrees with $l$ except that slot $s$ receives the label $d$.
--
--   **Theorem.** Let $\mathrm{src},\mathrm{dst}\in B$ and let $D$ be an $R$-linear derivation of $R[X]$ such that, for all $b\in B$ and $i\in I$, $D(X_{b,i})=X_{\mathrm{dst},i}$ if $b=\mathrm{src}$ and $D(X_{b,i})=0$ otherwise. Then
--
--   $$D\big(P_c(l)\big)=\sum_{\substack{s\in S\\ l(s)=\mathrm{src}}}P_c\big(l[s\mapsto\mathrm{dst}]\big).$$
--
--   The two blocks need not be distinct; for $\mathrm{src}=\mathrm{dst}$ the identity says that $D(P_c(l))$ is the number of $\mathrm{src}$-labelled slots times $P_c(l)$.
--
--   The derivation $D$ is the directional operator $\sum_iX_{\mathrm{dst},i}\,\partial/\partial X_{\mathrm{src},i}$, which moves one unit of degree from block $\mathrm{src}$ to block $\mathrm{dst}$. The theorem describes its effect on slot polynomials combinatorially: each occurrence of the source block is replaced by the destination block, one slot at a time, while the coefficient array stays the same. Slot polynomials are the coordinate expansions of multilinear forms evaluated on vector variables, so this formula drives the derivative computations of the transfer arguments.
--
--   **Formalization Note** $P_c(l)$ is `SlotPolynomial.polynomial c l`, with coefficients entering through the constant embedding `MvPolynomial.C`; $l[s\mapsto d]$ is `Function.update l s d`, and the sum runs over `Finset.univ.filter (fun s => l s = src)`. Decidable equality on $S$ and $B$ is assumed.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/RepresentationTheory/FoulkesHowe/SlotDerivative.lean#L44-L81

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

theorem OAI.Problem346.SlotPolynomial.derivation_polynomial [DecidableEq B]
    (c : (S → I) → R) (l : S → B) (src dst : B)
    (D : Derivation R (MvPolynomial (B × I) R) (MvPolynomial (B × I) R))
    (hD : ∀ b i, D (MvPolynomial.X (b, i)) =
      if b = src then MvPolynomial.X (dst, i) else 0) :
    D (polynomial c l) =
      ∑ s ∈ Finset.univ.filter (fun s => l s = src),
        polynomial c (Function.update l s dst) := by sorry
