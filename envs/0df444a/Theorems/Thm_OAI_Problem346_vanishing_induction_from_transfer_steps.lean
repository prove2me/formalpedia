-- Prove2me | Theorems.Thm_OAI_Problem346_vanishing_induction_from_transfer_steps
-- name    : OAI.Problem346.vanishing_induction_from_transfer_steps
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T16:29:08.574813+00:00
-- url     : https://prove2.me/theorems/ffd2872a-ca87-482a-872d-0088746a0f78
-- title:
--   Induction on the number of arguments: diagonal vanishing of symmetric forms when $a(a-1)\le b$, given two transfer steps
-- statement:
--   Let $V$ be a complex vector space. Write $\operatorname{Sym}(V)$ for the symmetric algebra of $V$ over $\mathbb{C}$. For $n\in\mathbb{N}$ let $\operatorname{Sym}^nV\subseteq\operatorname{Sym}(V)$ be the complex linear span of all products $v_0v_1\cdots v_{n-1}$ of $n$ vectors of $V$. For $n=0$ this is the span of the empty product $1$. For $(v_0,\dots,v_{n-1})\in V^n$ write $[v_0,\dots,v_{n-1}]=v_0\cdots v_{n-1}\in\operatorname{Sym}^nV$ and call it a monomial. For $v\in V$ and $k\in\mathbb{N}$ write $v^{k}=[v,\dots,v]\in\operatorname{Sym}^kV$ ($k$ factors). For $P\in\operatorname{Sym}^rV$ and $Q\in\operatorname{Sym}^mV$ the product $PQ$ in $\operatorname{Sym}(V)$ lies in $\operatorname{Sym}^{r+m}V$.
--
--   An *$a$-linear form on $\operatorname{Sym}^bV$* is a multilinear map $T\colon(\operatorname{Sym}^bV)^a\to\mathbb{C}$. It is *symmetric* if it is invariant under all permutations of its $a$ arguments, and it *vanishes on diagonal products* if $T(P,\dots,P)=0$ for every monomial $P=[y_0,\dots,y_{b-1}]$. For $r,m\in\mathbb{N}$, an $(r+1)$-linear form $T$ on $\operatorname{Sym}^{r+m}V$ and $x,t\in V$, define the $r$-linear form $T_{x,t}$ on $\operatorname{Sym}^mV$ by
--
--   $$
--   T_{x,t}(Q_1,\dots,Q_r)=T\bigl(t^{\,r+m},\ x^{r}Q_1,\ \dots,\ x^{r}Q_r\bigr),\qquad Q_1,\dots,Q_r\in\operatorname{Sym}^mV .
--   $$
--
--   **Theorem.** Assume the following three statements about $V$.
--
--   - (A) For all $r,m\ge1$ with $(r+1)r\le r+m$ and every symmetric $(r+1)$-linear form $T$ on $\operatorname{Sym}^{r+m}V$ that vanishes on diagonal products: $T_{x,t}(Q,\dots,Q)=0$ for all $x,t\in V$ and every monomial $Q=[y_0,\dots,y_{m-1}]$.
--   - (B) For all $r,m\ge1$ with $(r+1)r\le r+m$ and every symmetric $(r+1)$-linear form $T$ on $\operatorname{Sym}^{r+m}V$ such that $T_{x,t}=0$ for all $x,t\in V$: $T(v_0^{\,r+m},\dots,v_r^{\,r+m})=0$ for all $v_0,\dots,v_r\in V$.
--   - (C) For all $a,b\in\mathbb{N}$, every $a$-linear form $T$ on $\operatorname{Sym}^bV$, symmetric or not, with $T(v_0^{\,b},\dots,v_{a-1}^{\,b})=0$ for all $v_0,\dots,v_{a-1}\in V$ is zero.
--
--   Then for all $a,b\in\mathbb{N}$ with
--
--   $$
--   a\ge1,\qquad b\ge1,\qquad a(a-1)\le b,
--   $$
--
--   every symmetric $a$-linear form on $\operatorname{Sym}^bV$ that vanishes on diagonal products is identically zero.
--
--   The theorem isolates the induction on the number $a$ of arguments in the proof of the diagonal vanishing theorem. Each step passes from $(a,b)=(r+1,r+m)$ to $(r,m)$, and the quadratic bound $a(a-1)\le b$ is preserved by this step, because $(r+1)r\le r+m$ implies $r(r-1)\le m$. The first transfer (A), the second transfer (B) and the spanning of $\operatorname{Sym}^bV$ by pure powers (C) are proved separately and plugged in. The resulting vanishing theorem is the hypothesis of the duality criterion that makes the Foulkes map surjective.
--
--   **Formalization Note** $\operatorname{Sym}^nV$ is `SymPow n V`, the subtype of the submodule `symPowSubmodule n V` of Mathlib's `SymmetricAlgebra ℂ V`, and $[v_0,\dots,v_{n-1}]$ is `symMonomial n V v`. The form $T_{x,t}$ is `lowerProductForm r m T x t`, and the slot holding $t^{r+m}$ is the first one (`Fin.cons`). Symmetry is the predicate `IsSymmetricMultilinearForm`. The hypotheses (A), (B), (C) are the arguments `firstTransfer`, `secondTransfer`, `purePowerExt`. The bound $a(a-1)\le b$ uses truncated natural-number subtraction, which is harmless because $a\ge1$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/RepresentationTheory/FoulkesHowe/Vanishing.lean#L13-L66

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

open OAI OAI.Problem346
universe u
variable {V : Type u} [AddCommGroup V] [Module ℂ V]

theorem OAI.Problem346.vanishing_induction_from_transfer_steps
    (firstTransfer : ∀ r m : ℕ, 0 < r → 0 < m → (r+1)*r ≤ r+m →
      ∀ T : SymmetricMultilinearForm (r+1) (r+m) V,
      IsSymmetricMultilinearForm (r+1) (r+m) V T →
      (∀ y : Fin (r+m) → V, T (fun _ => symMonomial (r+m) V y) = 0) →
      ∀ x t : V, ∀ y : Fin m → V,
        lowerProductForm r m T x t (fun _ => symMonomial m V y) = 0)
    (secondTransfer : ∀ r m : ℕ, 0 < r → 0 < m → (r+1)*r ≤ r+m →
      ∀ T : SymmetricMultilinearForm (r+1) (r+m) V,
      IsSymmetricMultilinearForm (r+1) (r+m) V T →
      (∀ x t : V, ∀ Q : Fin r → SymPow m V, lowerProductForm r m T x t Q = 0) →
      ∀ v : Fin (r+1) → V,
        T (fun i => symMonomial (r+m) V (fun _ => v i)) = 0)
    (purePowerExt : ∀ a b : ℕ, ∀ T : SymmetricMultilinearForm a b V,
      (∀ v : Fin a → V, T (fun i => symMonomial b V (fun _ => v i)) = 0) → T = 0) :
    ∀ a b : ℕ, 1 ≤ a → 1 ≤ b → a*(a-1) ≤ b →
      ∀ T : SymmetricMultilinearForm a b V,
      IsSymmetricMultilinearForm a b V T →
      (∀ y : Fin b → V, T (fun _ => symMonomial b V y) = 0) → T = 0 := by sorry
