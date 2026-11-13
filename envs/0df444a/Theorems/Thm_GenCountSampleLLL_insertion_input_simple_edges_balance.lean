-- Prove2me | Theorems.Thm_GenCountSampleLLL_insertion_input_simple_edges_balance
-- name    : GenCountSampleLLL.insertion_input_simple_edges_balance
-- status  : Open
-- author  : @wcysai
-- created : 2026-11-13T05:52:48.169772+00:00
-- url     : https://prove2.me/theorems/77fb68f8-463f-45da-8386-3ee3944ebe50
-- title:
--   Detailed balance for the two simple input edges
-- statement:
--   For an input assignment satisfying $D\setminus\{a\}$, the auxiliary insertion chain satisfies weighted detailed balance between the input state and its corresponding output state when the input satisfies $a$, and between the input state and its corresponding singleton-tree state when it violates $a$. These are the simple input edges in the proof of Lemma 6.4.
-- source:
--   Jain, Mizgerd, Pham, A general counting and sampling Lovász local lemma, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/702.pdf, Algorithm 3 and proof of Lemma 6.4, pp.20 and 23.

import Definitions.Def_GenCountSampleLLL_insertionChain
noncomputable section
open scoped Classical BigOperators ENNReal

namespace GenCountSampleLLL
theorem insertion_input_simple_edges_balance (I : Inst) (D : Finset (Fin I.m)) (a : Fin I.m)
    (ha : a ∈ D) (σ : I.Assign) (hgood : σ ∈ I.Good (D.erase a))
    (X : I.S D a) (hX : X.1 = ⟨[], Inst.Base.inp σ⟩) :
    (¬ I.bad a σ → ∀ Y : I.S D a, Y.1 = ⟨[], Inst.Base.out σ⟩ →
      I.w D a X * I.Pker D a X Y = I.w D a Y * I.Pker D a Y X) ∧
    (I.bad a σ → ∀ Y : I.S D a, Y.1 = ⟨[], Inst.Base.tree {a} σ⟩ →
      I.w D a X * I.Pker D a X Y = I.w D a Y * I.Pker D a Y X) := by sorry
end GenCountSampleLLL
