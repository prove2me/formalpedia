-- Prove2me | Theorems.Thm_OAI_Problem346_flattened_derivative_eq_card_smul
-- name    : OAI.Problem346.flattened_derivative_eq_card_smul
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T16:47:31.338802+00:00
-- url     : https://prove2.me/theorems/5f66c7cf-c65b-419b-8b7a-bbc2b7d4af75
-- title:
--   Shifting a block confined to one row gives a single replacement times the number of occurrences
-- statement:
--   Let $V$ be a complex vector space and $a,b\in\mathbb{N}$. Write $\mathrm{Sym}^bV$ for the subspace of the symmetric algebra of $V$ spanned by the products $v_1\cdots v_b$ of $b$ vectors. Let $T\colon(\mathrm{Sym}^bV)^a\to\mathbb{C}$ be any multilinear form (no symmetry is assumed), and let $T^\flat$ be its *flattening*: the multilinear form in $ab$ vectors $v=(v_{i,j})$, indexed by *slots* $(i,j)$ with row $i\in\{0,\dots,a-1\}$ and column $j\in\{0,\dots,b-1\}$, given by
--
--   $$T^\flat(v)=T\big(v_{0,0}\cdots v_{0,b-1},\ \dots,\ v_{a-1,0}\cdots v_{a-1,b-1}\big).$$
--
--   Let $K$ be a finite set, $e\colon K\to V$ a family of vectors and $B$ any set of block labels. For a labelling $l$ of the slots by blocks, define the coordinate polynomial
--
--   $$P(l)=\sum_{k}T^\flat\big((e_{k(p)})_{p}\big)\prod_{p}X_{l(p),\,k(p)}\in\mathbb{C}[X_{q,\kappa} : (q,\kappa)\in B\times K],$$
--
--   where $k$ runs over all functions from the set of slots to $K$ and $p$ over the slots. (Substituting the vector variable $x_q=\sum_\kappa X_{q,\kappa}e_\kappa$ for each block $q$ and expanding $T^\flat\big((x_{l(p)})_p\big)$ by multilinearity gives $P(l)$.)
--
--   **Theorem.** Let $\mathrm{src},\mathrm{dst}\in B$ and let $(i,j)$ be a slot with $l(i,j)=\mathrm{src}$ such that every slot labelled $\mathrm{src}$ lies in row $i$. Let $D$ be a $\mathbb{C}$-linear derivation of $\mathbb{C}[X_{q,\kappa}]$ with $D(X_{q,\kappa})=X_{\mathrm{dst},\kappa}$ if $q=\mathrm{src}$ and $D(X_{q,\kappa})=0$ otherwise. Then
--
--   $$D\big(P(l)\big)=N\cdot P\big(l[(i,j)\mapsto\mathrm{dst}]\big),\qquad N=\#\{p : l(p)=\mathrm{src}\},$$
--
--   where $l[(i,j)\mapsto\mathrm{dst}]$ agrees with $l$ except that the slot $(i,j)$ is relabelled $\mathrm{dst}$.
--
--   Within one row, the vector arguments of $T^\flat$ are factors of a single commutative product, so all occurrences of the source block in that row are interchangeable. The theorem therefore turns the general derivative formula (a sum of single-slot replacements) into a scalar multiple of one replacement, which is the form needed to pass from one labelling to the next in the transfer sequences.
--
--   **Formalization Note** $T$ has type `SymmetricMultilinearForm a b V`, which is the type of all multilinear maps $(\mathrm{Sym}^bV)^a\to\mathbb{C}$; the name does not impose symmetry. $T^\flat$ is `flattenedForm T`, $P(l)$ is `multilinearPolynomial (flattenedForm T) e l` with slots `Fin a × Fin b`, and $N$ acts as a natural-number multiple. Decidable equality on $B$ is assumed.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/RepresentationTheory/FoulkesHowe/TransferDerivative.lean#L58-L87

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

open OAI OAI.Problem346
open scoped BigOperators

theorem OAI.Problem346.flattened_derivative_eq_card_smul
    (a b : ℕ) (V K B : Type*) [AddCommGroup V] [Module ℂ V]
    [Fintype K] [DecidableEq B]
    (T : SymmetricMultilinearForm a b V) (e : K → V)
    (l : Fin a × Fin b → B) (src dst : B) (i : Fin a) (j : Fin b)
    (hj : l (i,j) = src)
    (hrow : ∀ p, l p = src → p.1 = i)
    (D : Derivation ℂ (MvPolynomial (B × K) ℂ) (MvPolynomial (B × K) ℂ))
    (hD : ∀ q k, D (MvPolynomial.X (q,k)) =
      if q = src then MvPolynomial.X (dst,k) else 0) :
    D (multilinearPolynomial (flattenedForm T) e l) =
      (Finset.univ.filter (fun p => l p = src)).card •
        multilinearPolynomial (flattenedForm T) e
          (Function.update l (i,j) dst) := by sorry
