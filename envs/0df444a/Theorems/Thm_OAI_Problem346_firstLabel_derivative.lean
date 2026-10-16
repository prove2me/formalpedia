-- Prove2me | Theorems.Thm_OAI_Problem346_firstLabel_derivative
-- name    : OAI.Problem346.firstLabel_derivative
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T16:48:02.269495+00:00
-- url     : https://prove2.me/theorems/2177e09b-d2d7-4976-872c-94f5d0cdafe1
-- title:
--   Derivative step of the first transfer: shifting $t$ to $y_k$ gives $r+m-k$ times the next stage
-- statement:
--   Let $V$ be a complex vector space and $r,m\in\mathbb{N}$, and write $\mathrm{Sym}^nV$ for the span, in the symmetric algebra of $V$, of the products of $n$ vectors. Let $T\colon(\mathrm{Sym}^{r+m}V)^{r+1}\to\mathbb{C}$ be a multilinear form (not necessarily symmetric) with flattening
--
--   $$T^\flat(v)=T\big(v_{0,0}\cdots v_{0,r+m-1},\ \dots,\ v_{r,0}\cdots v_{r,r+m-1}\big)$$
--
--   on arrays $v=(v_{i,j})$ of vectors indexed by *slots* $(i,j)$, $0\le i\le r$, $0\le j\le r+m-1$.
--
--   The block labels are $x$, $t$, $y_0,\dots,y_{m-1}$. For $k\in\mathbb{N}$ the labelling $\lambda_k$ puts $y_j$ at the slot $(0,j)$ when $j<k$ and $j<m$, puts $t$ at the remaining slots of row $0$, and in each row $i\ge1$ puts $x$ in the columns $j<r$ and $y_{j-r}$ in the columns $j\ge r$. Let $K$ be a finite set and $e\colon K\to V$ a family of vectors. The $k$-th first-transfer polynomial is
--
--   $$P_k=\sum_{\phi}T^\flat\big((e_{\phi(p)})_p\big)\prod_pX_{\lambda_k(p),\,\phi(p)}\in\mathbb{C}\big[X_{q,\kappa} : q\in\{x,t,y_0,\dots,y_{m-1}\},\ \kappa\in K\big],$$
--
--   where $\phi$ ranges over all functions from the set of slots to $K$ and $p$ over the slots.
--
--   **Theorem.** Let $k<m$ and let $D$ be a $\mathbb{C}$-linear derivation of this polynomial ring with $D(X_{t,\kappa})=X_{y_k,\kappa}$ for all $\kappa\in K$ and $D(X_{q,\kappa})=0$ for every label $q\ne t$. Then
--
--   $$D(P_k)=(r+m-k)\,P_{k+1}.$$
--
--   Reading rows as products of vector variables, $P_k$ encodes $T$ evaluated on the row product $y_0\cdots y_{k-1}\,t^{r+m-k}$ together with $r$ copies of $x^ry_0\cdots y_{m-1}$. The derivative moves one factor $t$ of row $0$ to $y_k$; because all $r+m-k$ copies of $t$ sit in the same row, the result is that multiple of the next stage. Combined with block-degree counts, this is what lets vanishing propagate backwards from $P_m$ to $P_0$ in the first transfer.
--
--   **Formalization Note** The labels form `FirstBlock m = Option (Option (Fin m))` (`none` is $x$, `some none` is $t$, `some (some j)` is $y_j$), $\lambda_k$ is `firstLabel r m k`, and $P_k$ is `multilinearPolynomial (flattenedForm T) e (firstLabel r m k)`. Since $k<m$, the factor $r+m-k$ is a positive integer (natural-number subtraction does not truncate here), cast to $\mathbb{C}$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/RepresentationTheory/FoulkesHowe/TransferDerivative.lean#L89-L115

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

theorem OAI.Problem346.firstLabel_derivative
    (r m k : ℕ) (hk : k < m) (V K : Type*)
    [AddCommGroup V] [Module ℂ V] [Fintype K]
    (T : SymmetricMultilinearForm (r+1) (r+m) V) (e : K → V)
    (D : Derivation ℂ (MvPolynomial (FirstBlock m × K) ℂ)
      (MvPolynomial (FirstBlock m × K) ℂ))
    (hD : ∀ q j, D (MvPolynomial.X (q,j)) =
      if q = some none then MvPolynomial.X (some (some ⟨k,hk⟩),j) else 0) :
    D (multilinearPolynomial (flattenedForm T) e
        (firstLabel r m k)) =
      ((r+m-k : ℕ) : ℂ) •
        multilinearPolynomial (flattenedForm T) e
          (firstLabel r m (k+1)) := by sorry
