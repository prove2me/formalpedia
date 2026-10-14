-- Prove2me | Theorems.Thm_MoritaEquiv_ElemEmb_exists_of_sortwise_equiv
-- name    : MoritaEquiv.ElemEmb.exists_of_sortwise_equiv
-- status  : Proved
-- author  : @Alien60
-- created : 2026-10-13T19:12:55.416284+00:00
-- url     : https://prove2.me/theorems/101a2f22-cd0c-41c8-b0c2-bb1942a3583e
-- title:
--   Strong isomorphisms of many-sorted structures are elementary embeddings
-- statement:
--   Let $\Sigma$ be a many-sorted signature and $A$, $B$ two $\Sigma$-structures. Suppose we are given, for every sort $s$, a bijection $E_s : A_s \to B_s$ such that
--   1. $E_s(f^A(a_1,\dots,a_m)) = f^B(E(a_1),\dots,E(a_m))$ for every function symbol $f$, and
--   2. $r^B(E(a_1),\dots,E(a_m)) \iff r^A(a_1,\dots,a_m)$ for every relation symbol $r$.
--
--   **Statement.** Then $E$ is an elementary embedding $A \to B$: for every formula $\varphi$ in context and every assignment $v$, $B \models \varphi[E\circ v] \iff A\models\varphi[v]$. Equivalently, every isomorphism of $\Sigma$-structures is elementary.
--
--   This is the standard fact that isomorphic structures satisfy the same formulas. It is proved by induction on terms and then on formulas, using surjectivity of $E$ in the quantifier step. It is the basic tool for producing arrows in the category $\mathrm{Mod}(T)$ of models of a theory, whose morphisms are elementary embeddings.
--
--   **Formalization Note** The conclusion is stated as the existence of an `ElemEmb A B` whose underlying sortwise function is exactly `E`.
-- source:
--   T. W. Barrett, H. Halvorson, Morita Equivalence, Rev. Symb. Logic 9 (2016) 556-582, https://arxiv.org/abs/1506.04675, §5 (proof of Theorem 5.2)

import Mathlib
import Definitions.Def_MoritaEquiv_defs

open CategoryTheory

namespace MoritaEquiv

/-- A sortwise bijection between two `L`-structures that commutes with every function symbol and
preserves and reflects every relation symbol (a strong isomorphism) underlies an elementary
embedding. -/
theorem ElemEmb.exists_of_sortwise_equiv {L : Sig} {A B : Str L}
    (E : ∀ s, A.carrier s ≃ B.carrier s)
    (hf : ∀ {m : ℕ} {dom : Fin m → L.Srt} {s : L.Srt} (f : L.Func m dom s)
      (xs : (j : Fin m) → A.carrier (dom j)),
      E s (A.funMap f xs) = B.funMap f (fun j => E _ (xs j)))
    (hr : ∀ {m : ℕ} {dom : Fin m → L.Srt} (r : L.Rel m dom) (xs : (j : Fin m) → A.carrier (dom j)),
      B.relMap r (fun j => E _ (xs j)) ↔ A.relMap r xs) :
    ∃ h : ElemEmb A B, ∀ s x, h.toFun s x = E s x := by sorry

end MoritaEquiv
