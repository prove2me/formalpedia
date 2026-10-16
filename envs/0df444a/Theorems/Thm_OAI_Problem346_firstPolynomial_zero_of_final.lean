-- Prove2me | Theorems.Thm_OAI_Problem346_firstPolynomial_zero_of_final
-- name    : OAI.Problem346.firstPolynomial_zero_of_final
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T16:49:25.188778+00:00
-- url     : https://prove2.me/theorems/ee1177ca-e7e4-46fc-852d-fbd77c6bbe45
-- title:
--   First transfer: vanishing of the final-stage polynomial forces vanishing at the initial stage
-- statement:
--   Let $V$ be a complex vector space and $r,m\in\mathbb{N}$, and write $\mathrm{Sym}^nV$ for the span, inside the symmetric algebra of $V$, of the products of $n$ vectors. Let $T\colon(\mathrm{Sym}^{r+m}V)^{r+1}\to\mathbb{C}$ be a multilinear form (no symmetry is assumed) with flattening
--
--   $$T^\flat(v)=T\big(v_{0,0}\cdots v_{0,r+m-1},\ \dots,\ v_{r,0}\cdots v_{r,r+m-1}\big),$$
--
--   a multilinear form in vectors $v_{i,j}$ indexed by *slots* $(i,j)$, $0\le i\le r$, $0\le j\le r+m-1$. Use the block labels $x,t,y_0,\dots,y_{m-1}$, and for $k\in\mathbb{N}$ let $\lambda_k$ be the labelling of the slots with $\lambda_k(0,j)=y_j$ if $j<k$ and $j<m$, $\lambda_k(0,j)=t$ otherwise, and, for rows $i\ge1$, $\lambda_k(i,j)=x$ if $j<r$ and $\lambda_k(i,j)=y_{j-r}$ if $j\ge r$. Let $K$ be a finite set, $e\colon K\to V$ a family of vectors, and
--
--   $$P_k=\sum_{\phi}T^\flat\big((e_{\phi(p)})_p\big)\prod_pX_{\lambda_k(p),\,\phi(p)}\in\mathbb{C}\big[X_{q,\kappa} : q\in\{x,t,y_0,\dots,y_{m-1}\},\ \kappa\in K\big],$$
--
--   the sum running over all functions $\phi$ from the set of slots to $K$.
--
--   **Theorem.**
--
--   $$P_m=0\quad\Longrightarrow\quad P_0=0 .$$
--
--   After the substitution $x=\sum_\kappa X_{x,\kappa}e_\kappa$, $t=\sum_\kappa X_{t,\kappa}e_\kappa$, $y_j=\sum_\kappa X_{y_j,\kappa}e_\kappa$, the polynomial $P_0$ is the coordinate expansion of $T\big(t^{r+m},\,x^ry_0\cdots y_{m-1},\,\dots,\,x^ry_0\cdots y_{m-1}\big)$ and $P_m$ that of $T\big(t^ry_0\cdots y_{m-1},\,x^ry_0\cdots y_{m-1},\,\dots,\,x^ry_0\cdots y_{m-1}\big)$, with $r$ copies of $x^ry_0\cdots y_{m-1}$ in both. The theorem is the polynomial core of the first transfer step of the stabilization argument: vanishing when the first argument shares the common factor $y_0\cdots y_{m-1}$ with the others implies vanishing when the first argument is the pure power $t^{r+m}$. No symmetry of $T$, no restriction on $r,m$ and no finite-dimensionality of $V$ is needed.
--
--   **Formalization Note** $P_k$ is `firstPolynomial T e k`, i.e. `multilinearPolynomial (flattenedForm T) e (firstLabel r m k)`, with labels in `FirstBlock m = Option (Option (Fin m))` (`none` is $x$, `some none` is $t$, `some (some j)` is $y_j$). The type `SymmetricMultilinearForm (r+1) (r+m) V` consists of all multilinear maps $(\mathrm{Sym}^{r+m}V)^{r+1}\to\mathbb{C}$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/RepresentationTheory/FoulkesHowe/FirstTransfer.lean#L37-L54

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
variable {V : Type u} [AddCommGroup V] [Module ℂ V]
variable {κ : Type v} [Fintype κ]

theorem OAI.Problem346.firstPolynomial_zero_of_final {r m : ℕ}
    (T : SymmetricMultilinearForm (r+1) (r+m) V) (e : κ → V)
    (hm : firstPolynomial T e m = 0) : firstPolynomial T e 0 = 0 := by sorry
