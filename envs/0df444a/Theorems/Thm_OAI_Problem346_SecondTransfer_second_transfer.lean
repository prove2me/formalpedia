-- Prove2me | Theorems.Thm_OAI_Problem346_SecondTransfer_second_transfer
-- name    : OAI.Problem346.SecondTransfer.second_transfer
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T17:05:52.257444+00:00
-- url     : https://prove2.me/theorems/400b6b82-cf59-4fbe-8bb9-287f1cf399e3
-- title:
--   Second transfer: vanishing on $(t^{r+m}, x^rQ_1,\dots,x^rQ_r)$ forces vanishing on independent pure powers
-- statement:
--   Let $V$ be a finite-dimensional complex vector space. For $n\in\mathbb{N}$ let $\mathrm{Sym}^nV$ be the span, inside the symmetric algebra $S(V)$ of $V$ over $\mathbb{C}$, of all products $v_1\cdots v_n$ of $n$ vectors; for $x\in V$ write $x^n\in\mathrm{Sym}^nV$ for the product of $n$ copies of $x$, and for $P\in\mathrm{Sym}^pV$ and $Q\in\mathrm{Sym}^qV$ let $PQ\in\mathrm{Sym}^{p+q}V$ be their product in $S(V)$.
--
--   Let $r,m\in\mathbb{N}$ satisfy $r(r+1)\le r+m$, and let $T:(\mathrm{Sym}^{r+m}V)^{r+1}\to\mathbb{C}$ be a $\mathbb{C}$-multilinear form (not assumed to be symmetric). Suppose that
--
--   $$
--   T\bigl(t^{r+m},\,x^rQ_1,\,x^rQ_2,\,\dots,\,x^rQ_r\bigr)=0\qquad\text{for all }x,t\in V\text{ and all }Q_1,\dots,Q_r\in\mathrm{Sym}^mV .
--   $$
--
--   Then
--
--   $$
--   T\bigl(v_0^{\,r+m},\,v_1^{\,r+m},\,\dots,\,v_r^{\,r+m}\bigr)=0\qquad\text{for all }v_0,v_1,\dots,v_r\in V .
--   $$
--
--   The hypothesis only controls $T$ when its last $r$ arguments share the common factor $x^r$; the conclusion removes this common power and gives vanishing on arbitrary independent pure powers. Since pure powers span each symmetric power, the conclusion forces $T=0$ by multilinearity. In the inductive proof that a symmetric form on $(\mathrm{Sym}^bV)^a$ vanishing on diagonal arguments is zero when $a(a-1)\le b$, this is the step passing from the vanishing of the lower forms $(Q_1,\dots,Q_r)\mapsto T(t^{r+m},x^rQ_1,\dots,x^rQ_r)$, supplied by the induction hypothesis, to the vanishing of $T$; the threshold $r(r+1)\le r+m$ is the case $a=r+1$, $b=r+m$ of $a(a-1)\le b$.
--
--   **Formalization Note** The first argument $t^{r+m}$ is placed in slot $0$ with `Fin.cons`; $x^n$ is `symMonomial n V (fun _ => x)` and the product $\mathrm{Sym}^rV\times\mathrm{Sym}^mV\to\mathrm{Sym}^{r+m}V$ is the bilinear map `symPowMul r m`. `SymmetricMultilinearForm (r+1) (r+m) V` denotes all multilinear forms; no symmetry is assumed. Finite dimensionality is used to choose a finite basis of $V$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/RepresentationTheory/FoulkesHowe/SecondTransfer.lean#L56-L77

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

theorem OAI.Problem346.SecondTransfer.second_transfer [FiniteDimensional ℂ V] (r m : ℕ)
    (hb : r * (r+1) ≤ r+m)
    (T : SymmetricMultilinearForm (r+1) (r+m) V)
    (h : ∀ x t : V, ∀ Q : Fin r → SymPow m V,
      T (Fin.cons (symMonomial (r+m) V (fun _ => t))
        (fun i => symPowMul r m (symMonomial r V (fun _ => x)) (Q i))) = 0) :
    ∀ v : Fin (r+1) → V,
      T (fun i => symMonomial (r+m) V (fun _ => v i)) = 0 := by sorry
