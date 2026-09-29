-- Prove2me | Theorems.Thm_NumberField_mixedEmbedding_sgn_eq_one_of_forall_pos_of_polarCoord
-- name    : NumberField.mixedEmbedding.sgn_eq_one_of_forall_pos_of_polarCoord
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.964832+00:00
-- url     : https://prove2.me/theorems/dd59235c-de66-534d-b12d-e9192b5c7be5
-- title:
--   Totally positive units have trivial sign in polar coordinates
-- statement:
--   Let $K$ be a number field and let $r = \#\{\text{infinite places of }K\}$, with $\mathrm{nrComplexPlaces}\,K$ the number of complex places; write $V$ for the mixed space `mixedSpace K`, whose first component is indexed by the real places. Suppose given a family of maps $P_s : (\mathrm{Fin}\,r \to \mathbb{R}) \times (\mathrm{Fin}\,(\mathrm{nrComplexPlaces}\,K) \to \mathbb{R}) \to V$ indexed by $s$ in the group of functions from the real places of $K$ to $\mathbb{Z}^\times$, together with maps $\mathrm{sgn} : V \to (\{\text{real places}\} \to \mathbb{Z}^\times)$ and $\arg : V \to (\mathrm{Fin}\,(\mathrm{nrComplexPlaces}\,K) \to \mathbb{R})$, subject to: each $P_s$ is continuous; $P_{ss'}(x+x',\theta+\theta') = P_s(x,\theta)\,P_{s'}(x',\theta')$ for all $s,s',x,x',\theta,\theta'$; $\mathrm{normAtPlace}_w(P_s(x,\theta)) = \exp\big(x_{e(w)}/\mathrm{mult}(w)\big)$ for every infinite place $w$, where $e$ is the chosen bijection `Fintype.equivFin` from the infinite places to $\mathrm{Fin}\,r$ (in particular the norms are independent of $s$ and $\theta$); and, for every unit $y$ of $V$, $P_{\mathrm{sgn}\,y}\big((\mathrm{mult}(e^{-1}i)\log \mathrm{normAtPlace}_{e^{-1}i}(y))_i,\ \arg y\big) = y$. Then every unit $y \in V$ whose real coordinates $y_w$ are all strictly positive satisfies $\mathrm{sgn}\,y = 1$.
--
--   The statement pins down the sign vector attached by an abstractly axiomatised exponential–polar coordinate system on the mixed space of a number field: on totally positive units it is trivial. It is used in the construction of the lattice-sum decompositions of unit sums over windows in the mixed space, where the relevant cosets are cut out by positivity at the real places.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_mixedEmbedding_sgn_eq_one_of_forall_pos_of_polarCoord.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding
open scoped Classical in

theorem NumberField.mixedEmbedding.sgn_eq_one_of_forall_pos_of_polarCoord
    (K : Type) [Field K] [NumberField K]
    (P : ({w : InfinitePlace K // w.IsReal} → ℤˣ) →
      (Fin (Fintype.card (InfinitePlace K)) → ℝ) × (Fin (nrComplexPlaces K) → ℝ) → mixedSpace K)
    (sgn : mixedSpace K → ({w : InfinitePlace K // w.IsReal} → ℤˣ))
    (arg : mixedSpace K → (Fin (nrComplexPlaces K) → ℝ))
    (hP_cont : ∀ s, Continuous (P s))
    (hP_mul : ∀ s s' (x x' : Fin (Fintype.card (InfinitePlace K)) → ℝ) (θ θ' : Fin (nrComplexPlaces K) → ℝ),
      P (s * s') (x + x', θ + θ') = P s (x, θ) * P s' (x', θ'))
    (hP_norm : ∀ s (x : Fin (Fintype.card (InfinitePlace K)) → ℝ) (θ : Fin (nrComplexPlaces K) → ℝ) (w : InfinitePlace K),
      normAtPlace w (P s (x, θ)) = Real.exp (x (Fintype.equivFin (InfinitePlace K) w) / (w.mult : ℝ)))
    (hP_inv : ∀ y : mixedSpace K, IsUnit y →
      P (sgn y) (fun i => (((Fintype.equivFin (InfinitePlace K)).symm i).mult : ℝ) *
          Real.log (normAtPlace ((Fintype.equivFin (InfinitePlace K)).symm i) y), arg y) = y) :
    ∀ y : mixedSpace K, IsUnit y → (∀ w : {w : InfinitePlace K // w.IsReal}, 0 < y.1 w) → sgn y = 1 := by sorry
