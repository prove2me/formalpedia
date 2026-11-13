-- Prove2me | Theorems.Thm_GenCountSampleLLL_lemma_6_3
-- name    : GenCountSampleLLL.lemma_6_3
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T04:41:24.843575+00:00
-- url     : https://prove2.me/theorems/c9af5922-f6c4-46f9-b1e3-603ee20e2b46
-- title:
--   Lemma 6.3, p.22 — inclusion probability and pinned list law
-- statement:
--   Let $D$ be a set of constraints, $T\in\mathcal T_{D,a}$ a rooted 2-tree, and $z\in E_T$ an assignment on $U_T$. Set $e=(T,z)$ and $q_e=\nu_{U_T}(z)$. Then $\Pr(e\in L)=q_e$, and the pinned list $L_e$ has the conditional distribution of $L$ given $e\in L$. The formal statement represents assignments on $U_T$ by normalized full assignments, and expresses the conditional-law equality by the equivalent joint-mass identity $\Pr(L=\ell,\ e\in L)=q_e\Pr(L_e=\ell)$ for every list $\ell$. The coordinate laws have full support, so $q_e>0$.
-- source:
--   Jain, Mizgerd, Pham, A general counting and sampling Lovász local lemma, https://arxiv.org/abs/2609.23671, Lemma 6.3, p.22.

import Mathlib
import Definitions.Def_GenCountSampleLLL_twoTrees
set_option autoImplicit false
open scoped BigOperators
open Classical

namespace GenCountSampleLLL

theorem lemma_6_3 (I : Inst) (D : Finset (Fin I.m)) (a : Fin I.m)
    (T : Finset (Fin I.m)) (z : I.Assign)
    (hT : T ∈ I.twoTrees D a) (hz : z ∈ I.labelsE D a T) :
    (∑ ω : I.ExpSpace, (I.expLaw ω).toReal *
      (if (T, z) ∈ I.Llist D a ω then (1 : ℝ) else 0)) = I.nuU (I.UT D T) z ∧
    ∀ L : Finset (Finset (Fin I.m) × I.Assign),
      (∑ ω : I.ExpSpace, (I.expLaw ω).toReal *
        (if I.Llist D a ω = L ∧ (T, z) ∈ I.Llist D a ω then (1 : ℝ) else 0)) =
      I.nuU (I.UT D T) z *
        (∑ ω : I.ExpSpace, (I.expLaw ω).toReal *
          (if I.Le D a (T, z) ω = L then (1 : ℝ) else 0)) := by
  sorry

end GenCountSampleLLL
