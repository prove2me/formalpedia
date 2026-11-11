-- Prove2me | Theorems.Thm_InfoLossLAR_WorstCase_lemma_6_2
-- name    : InfoLossLAR.WorstCase.lemma_6_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T02:03:46.473135+00:00
-- url     : https://prove2.me/theorems/edb9d9e6-eeb0-43c6-98fe-c298eae8d4d2
-- title:
--   Lemma 6.2 — the incidence matrix of an oriented tree is an integral basis of $A_{d-1}$
-- statement:
--   Let $\mathscr T$ be a tree on the vertex set $\{1,\dots,d\}$ with an arbitrary orientation and signed incidence matrix $D_{\mathscr T}$ ($+1$ at the tail, $-1$ at the head of each edge column). Then $\mathscr T$ has $d-1$ edges, and the columns of $D_{\mathscr T}$ form an integral basis of the zero-sum lattice $A_{d-1}=\{z\in\mathbb Z^d:\mathbf 1^\top z=0\}$: they are linearly independent over $\mathbb Z$ and span $A_{d-1}$. In particular
--   $$D_{\mathscr T}\mathbb Z^{d-1}=A_{d-1},\qquad\operatorname{rank}_{\mathbb R}(D_{\mathscr T})=d-1.$$
--
--   Differences from the source:
--   - encoding: "a tree on $d$ vertices with an arbitrary orientation" → a `SimpleGraph` on `Fin d` with `IsTree` and a tail/head choice for each edge; reason: same objects
--   - encoding: "integral basis" → $\mathbb Z$-linear independence plus span equal to $A_{d-1}$; reason: definition of a basis
--   - encoding: columns indexed $1,\dots,d-1$ → columns indexed by the edge set; reason: the paper's order of edges is arbitrary
-- source:
--   Chen Qian, Information Loss Is All You Need: TC⁰ Pseudorandomness from Worst-Case Lattices, arXiv:2611.05136 (held version, sha256 2ebdfbf3…), p. 26, Lemma 6.2

import Mathlib
import Definitions.Def_InfoLossLAR_WorstCase_Rounding
import Definitions.Def_InfoLossLAR_WorstCase_FixedT

set_option autoImplicit false

namespace InfoLossLAR.WorstCase

/-- Lemma 6.2 (Tree incidence basis), p. 26: an oriented tree `𝒯` on the `d` vertices `Fin d`
has `d − 1` edges, and the columns of its signed incidence matrix `D_𝒯` form an integral basis
of `A_{d−1} = {z ∈ ℤ^d : 1ᵀz = 0}`: they are `ℤ`-linearly independent and span `A_{d−1}`; in
particular `D_𝒯 ℤ^{d−1} = A_{d−1}` and `rank_ℝ(D_𝒯) = d − 1`. -/
theorem lemma_6_2 (d : ℕ) (𝒯 : OrientedTree d) :
    Fintype.card 𝒯.G.edgeSet = d - 1 ∧
    LinearIndependent ℤ (fun e : 𝒯.G.edgeSet => fun i : Fin d => 𝒯.incidence i e) ∧
    Submodule.span ℤ (Set.range fun e : 𝒯.G.edgeSet => fun i : Fin d => 𝒯.incidence i e) =
      zeroSumLattice d ∧
    LinearMap.range (Matrix.mulVecLin 𝒯.incidence) = zeroSumLattice d ∧
    (𝒯.incidence.map (Int.cast : ℤ → ℝ)).rank = d - 1 := by sorry

end InfoLossLAR.WorstCase
