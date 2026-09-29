-- Prove2me | Theorems.Thm_ModularCurve_exists_finset_place_eq_of_ord_jqModC_sub_pos
-- name    : ModularCurve.exists_finset_place_eq_of_ord_jqModC_sub_pos
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:50.587938+00:00
-- url     : https://prove2.me/theorems/77600c57-68d0-5a49-adce-e3dd72599bff
-- title:
--   Outside a finite set, places of k(jmath̄,jmath̄_N) are determined by their centre
-- statement:
--   Let $K$ be an algebraically closed field, $\ell$ a prime with $\operatorname{char} K = \ell$, and $N \geq 1$ an integer with $\ell \nmid N$. Inside the field $\operatorname{LaurentSeries} K$ consider $\bar\jmath :=$ `jqModC K`, the Laurent series $q^{-1}$ times the reduction to $K$ of the integral power series $E_4^3 \cdot \eta^{-24}$-type numerator `jNum`, and $\bar\jmath_N :=$ `jqNModC K N`, its image under the ring homomorphism `qExpand K N` that multiplies all exponents by $N$ (substitution $q \mapsto q^N$); let $C :=$ `modularFunctionFieldC K N` be the intermediate field $K(\bar\jmath, \bar\jmath_N)$ of $\operatorname{LaurentSeries} K$ over $K$. A place of $C$ over $K$ is a valuation subring of $C$ containing the image of $K$, different from $C$ itself, and a principal ideal ring; $\operatorname{ord}_Q$ denotes the associated normalised integer valuation. The assertion is that there is a finite set $B$ of places of $C$ over $K$ such that: every place $Q$ with $\operatorname{ord}_Q(\bar\jmath) < 0$ lies in $B$; every place $Q$ with $\operatorname{ord}_Q(\bar\jmath_N) < 0$ lies in $B$; and for every place $Q \notin B$, every place $Q'$ and all $s, t \in K$, if $\operatorname{ord}_Q(\bar\jmath - s) > 0$, $\operatorname{ord}_Q(\bar\jmath_N - t) > 0$, $\operatorname{ord}_{Q'}(\bar\jmath - s) > 0$ and $\operatorname{ord}_{Q'}(\bar\jmath_N - t) > 0$, then $Q' = Q$.
--
--   The field $C = K(\bar\jmath, \bar\jmath_N)$ is the characteristic-$\ell$ function field of the modular curve $X_0(N)$, realised as the function field of the affine plane curve cut out by the reduction of the classical modular polynomial $\Phi_N$, and the statement says that away from a finite bad set (containing the poles of $\bar\jmath$ and $\bar\jmath_N$, and implicitly the singular points of that plane model) a place is the unique one centred at the point $(s,t)$ it determines. It is used in the theory of specialisation of places on $X_0(N)$ in characteristic $\ell$, in particular by the results on place specialisations, their inertia actions and reduction modulo $\ell$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_finset_place_eq_of_ord_jqModC_sub_pos.lean

import Mathlib
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_X0ModL
import Definitions.Def_AlgebraicCurve_DivisorClassGroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open ModularCurve AlgebraicCurve

theorem ModularCurve.exists_finset_place_eq_of_ord_jqModC_sub_pos
    (K : Type*) [Field K] [IsAlgClosed K] (ℓ : ℕ) [Fact ℓ.Prime] [CharP K ℓ]
    (N : ℕ) [NeZero N] (hℓN : ¬ ℓ ∣ N) :
    ∃ B : Finset (Place K (modularFunctionFieldC K N)),
      (∀ Q : Place K (modularFunctionFieldC K N),
        Q.ord (⟨jqModC K, jqModC_mem K N⟩ : modularFunctionFieldC K N) < 0 → Q ∈ B) ∧
      (∀ Q : Place K (modularFunctionFieldC K N),
        Q.ord (⟨jqNModC K N, jqNModC_mem K N⟩ : modularFunctionFieldC K N) < 0 → Q ∈ B) ∧
      ∀ Q : Place K (modularFunctionFieldC K N), Q ∉ B →
        ∀ (Q' : Place K (modularFunctionFieldC K N)) (s t : K),
          0 < Q.ord (⟨jqModC K, jqModC_mem K N⟩ - algebraMap K (modularFunctionFieldC K N) s) →
          0 < Q.ord (⟨jqNModC K N, jqNModC_mem K N⟩ - algebraMap K (modularFunctionFieldC K N) t) →
          0 < Q'.ord (⟨jqModC K, jqModC_mem K N⟩ - algebraMap K (modularFunctionFieldC K N) s) →
          0 < Q'.ord (⟨jqNModC K N, jqNModC_mem K N⟩ - algebraMap K (modularFunctionFieldC K N) t) →
          Q' = Q := by sorry
