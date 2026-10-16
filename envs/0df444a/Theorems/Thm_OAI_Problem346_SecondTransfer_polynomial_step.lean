-- Prove2me | Theorems.Thm_OAI_Problem346_SecondTransfer_polynomial_step
-- name    : OAI.Problem346.SecondTransfer.polynomial_step
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T17:02:05.898971+00:00
-- url     : https://prove2.me/theorems/7d5cc319-0dd6-4e1d-83dc-e60565a116bc
-- title:
--   One cancellation step in the second transfer: the labelled polynomial at $k$ vanishes if it vanishes at $k+\delta_i$
-- statement:
--   Let $V$ be a complex vector space and, for $n\in\mathbb{N}$, let $\mathrm{Sym}^nV$ be the span, inside the symmetric algebra of $V$ over $\mathbb{C}$, of all products $v_1v_2\cdots v_n$ of $n$ vectors of $V$. Fix $r,b\in\mathbb{N}$ and a $\mathbb{C}$-multilinear form $T:(\mathrm{Sym}^bV)^{r+1}\to\mathbb{C}$; no symmetry of $T$ is assumed. On the grid $G=\{0,1,\dots,r\}\times\{0,1,\dots,b-1\}$ (rows times columns) the flattened form
--
--   $$
--   \widehat T(v)=T\bigl(v_{0,0}v_{0,1}\cdots v_{0,b-1},\ \dots,\ v_{r,0}v_{r,1}\cdots v_{r,b-1}\bigr),\qquad v=(v_{a,j})_{(a,j)\in G}\in V^{G},
--   $$
--
--   is multilinear in its $(r+1)b$ vector arguments.
--
--   Let $(e_c)_{c\in J}$ be any family of vectors of $V$ indexed by a finite set $J$, and let $B_r=\{\star\}\cup\{0,1,\dots,r\}$ be the set of blocks, $\star$ being a common block. To a labelling $\ell:G\to B_r$ attach the polynomial in the variables $X_{\beta,c}$ ($\beta\in B_r$, $c\in J$)
--
--   $$
--   P_\ell=\sum_{\kappa:G\to J}\widehat T\bigl((e_{\kappa(p)})_{p\in G}\bigr)\prod_{p\in G}X_{\ell(p),\kappa(p)}\ \in\ \mathbb{C}[X_{\beta,c}:\beta\in B_r,\ c\in J].
--   $$
--
--   Its value at a point $z$ is $\widehat T$ evaluated with the vector $\sum_{c\in J}z_{\ell(p),c}\,e_c$ in position $p$, so all positions with the same label receive the same generic vector. For $k=(k_1,\dots,k_r)\in\mathbb{N}^r$ the prefix labelling $\ell_k$ is $\ell_k(0,j)=0$ and, for $1\le i\le r$, $\ell_k(i,j)=\star$ if $j<k_i$ and $\ell_k(i,j)=i$ if $j\ge k_i$; write $k+\delta_i$ for $k$ with its $i$-th entry increased by one.
--
--   **Theorem.** Assume $r(r+1)\le b$ and $k_{i'}\le r$ for every $i'\in\{1,\dots,r\}$, and let $i\in\{1,\dots,r\}$ satisfy $k_i<r$. Then
--
--   $$
--   P_{\ell_{k+\delta_i}}=0\quad\Longrightarrow\quad P_{\ell_k}=0 .
--   $$
--
--   This is a single step of the second transfer: moving one more factor of row $i$ from the row's own vector to the common vector can be undone at the level of polynomial identities. The quadratic hypothesis $r(r+1)\le b$ guarantees that, at every count vector $k$ of the box $\{0,\dots,r\}^r$ with $k_i<r$, the source block $i$ occupies more positions than the common block, which is what makes the cancellation possible. Iterating the step over the box carries a vanishing statement at $(r,\dots,r)$ back to $(0,\dots,0)$.
--
--   **Formalization Note** `SymmetricMultilinearForm (r+1) b V` is the type of all $\mathbb{C}$-multilinear forms on $(\mathrm{Sym}^bV)^{r+1}$; symmetry is a separate predicate and is not assumed here. The moving rows are indexed by `i : Fin r` (row `i.succ`), blocks are `Option (Fin (r+1))` with `none` the common block, $P_{\ell_k}$ is `multilinearPolynomial (flattenedSymmetricForm T) e (label k)`, a polynomial over `Block r × κ`, and the family `e` need not be a basis.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/RepresentationTheory/FoulkesHowe/SecondTransfer.lean#L31-L54

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
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_SecondLabels
import Definitions.Def_OAI_RepresentationTheory_FoulkesHowe_SecondSwap

open OAI OAI.Problem346 OAI.Problem346.SecondTransfer
open scoped BigOperators
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V]

theorem OAI.Problem346.SecondTransfer.polynomial_step {κ : Type*} [Fintype κ] {r b : ℕ}
    (T : SymmetricMultilinearForm (r+1) b V) (e : κ → V)
    (hb : r * (r+1) ≤ b) (k : Fin r → ℕ) (hk : ∀ j, k j ≤ r)
    (i : Fin r) (hi : k i < r)
    (hnext : multilinearPolynomial (flattenedSymmetricForm T) e
      (label (Function.update k i (k i+1))) = 0) :
    multilinearPolynomial (flattenedSymmetricForm T) e (label k) = 0 := by sorry
