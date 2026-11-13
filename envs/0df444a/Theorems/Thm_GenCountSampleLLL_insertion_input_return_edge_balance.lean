-- Prove2me | Theorems.Thm_GenCountSampleLLL_insertion_input_return_edge_balance
-- name    : GenCountSampleLLL.insertion_input_return_edge_balance
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T05:49:41.294959+00:00
-- url     : https://prove2.me/theorems/d39f1baf-6ffe-4861-ad42-87ecd3fc09f1
-- title:
--   Detailed balance on the insertion chain return edge
-- statement:
--   For a valid corridor entry $e=(T,z)$ and two valid states with the same assignment $\sigma$, namely the input state $I(\sigma)$ and the last corridor layer $L^e_{\ell(T)}(\sigma)$, the auxiliary insertion kernel satisfies $w(I(\sigma))P(I(\sigma),L^e_{\ell(T)}(\sigma))=w(L^e_{\ell(T)}(\sigma))P(L^e_{\ell(T)}(\sigma),I(\sigma))$. This is the random-list return-edge case in the proof of Lemma 6.4.
-- source:
--   Jain, Mizgerd, Pham, A general counting and sampling Lovász local lemma, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/702.pdf, proof of Lemma 6.4, p.23.

import Definitions.Def_GenCountSampleLLL_insertionChain
noncomputable section
open scoped Classical BigOperators

namespace GenCountSampleLLL
theorem insertion_input_return_edge_balance (I : Inst) (D : Finset (Fin I.m)) (a : Fin I.m)
    (σ : I.Assign) (T : Finset (Fin I.m)) (z : I.Assign) (X Y : I.S D a)
    (hX : X.1 = ⟨[], Inst.Base.inp σ⟩)
    (hY : Y.1 = ⟨[], Inst.Base.lay T z (I.ell D a T) σ⟩)
    (hT : T ∈ I.twoTrees D a) (hz : z ∈ I.labelsE D a T) :
    I.w D a X * I.Pker D a X Y = I.w D a Y * I.Pker D a Y X := by sorry
end GenCountSampleLLL
