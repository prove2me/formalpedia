-- Prove2me | Theorems.Thm_GenCountSampleLLL_lemma_6_3_pin_support
-- name    : GenCountSampleLLL.lemma_6_3_pin_support
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T05:13:49.381001+00:00
-- url     : https://prove2.me/theorems/c0f7970f-2434-474d-99f3-5c41055032df
-- title:
--   Lemma 6.3 support: pinned list contains its label
-- statement:
--   Let $T$ be a rooted 2-tree, $z\in E_T$ an assignment on $U_T$, and $e=(T,z)$. In every outcome, $e\in L$ exactly when the tree assignment is $z$, while the pinned list $L_e$ always contains $e$. Moreover $q_e=\nu_{U_T}(z)>0$. This is the deterministic support and positivity portion of Lemma 6.3; it does not assert its probability or conditional-law identities.
-- source:
--   Jain, Mizgerd, Pham, A general counting and sampling Lovász local lemma, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/702.pdf, Lemma 6.3, p.22.

import Definitions.Def_GenCountSampleLLL_twoTrees
noncomputable section
open scoped Classical BigOperators

namespace GenCountSampleLLL
theorem lemma_6_3_pin_support (I : Inst) (D : Finset (Fin I.m)) (a : Fin I.m)
    (T : Finset (Fin I.m)) (z : I.Assign)
    (hT : T ∈ I.twoTrees D a) (hz : z ∈ I.labelsE D a T) :
    (∀ ω : I.ExpSpace, ((T,z) ∈ I.Llist D a ω ↔ I.sigT D T ω = z) ∧
      (T,z) ∈ I.Le D a (T,z) ω) ∧ 0 < I.nuU (I.UT D T) z := by sorry
end GenCountSampleLLL
