-- Prove2me | Theorems.Thm_NoHair_kerr_inner_horizon_normal_identity
-- name    : NoHair.kerr_inner_horizon_normal_identity
-- status  : Open
-- author  : @Igor Valuev
-- created : 2026-11-22T23:07:02.094982+00:00
-- url     : https://prove2.me/theorems/fb92e629-3134-4f4d-94fa-7b059ccc821a
-- title:
--   Signed surface gravity of the inner Kerr horizon
-- statement:
--   For the inner helical Killing vector $X=\partial_t+(2/5)\partial_\varphi$ of the mass $5/2$, spin $2$ Kerr metric, its norm vanishes on $r=1$ and $d[g(X,X)]=(3/5)X^\flat$ there. Thus the signed surface gravity is $-3/10$. This component identity is required in each chart of the positive-radius Kerr–Schild atlas.
-- source:
--   M. Visser, The Kerr spacetime: A brief introduction, §§4 and 9, in particular equations (107)–(115), https://arxiv.org/abs/0706.0622. B. Carter, Global Structure of the Kerr Family of Gravitational Fields, Phys. Rev. 174 (1968) 1559–1571, https://doi.org/10.1103/PhysRev.174.1559.

import Definitions.Def_NoHair_kerrNewman

open NoHair Set
open scoped ContDiff Manifold

theorem NoHair.kerr_inner_horizon_normal_identity :
    let X : VecField (kerrNewmanSpacetime 2) := fun x => WithLp.toLp 2 ![1, -(2/5)*x.val 2, (2/5)*x.val 1, 0]
    let g := kerrNewmanMetricField (5/2) 2 0
    ∀ x : kerrNewmanSpacetime 2, ksRadius 2 x.val=1 → g x (X x) (X x)=0 ∧
      ∀ e ∈ atlas E4 (kerrNewmanSpacetime 2), ∀ y ∈ e.target, e.symm y=x → ∀ i : Fin 4,
        coordPartial (fun z => g (e.symm z) (X (e.symm z)) (X (e.symm z))) i y =
          (3/5)*loweredCoeffs g X e.symm y i := by
  sorry
