-- Prove2me | Theorems.Thm_Ideal_exists_eq_span_singleton_and_mem_nonZeroDivisors_of_forall_mul_mem_of_surjective_of_isDiscreteValuationRing
-- name    : Ideal.exists_eq_span_singleton_and_mem_nonZeroDivisors_of_forall_mul_mem_of_surjective_of_isDiscreteValuationRing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.239308+00:00
-- url     : https://prove2.me/theorems/87bbec53-bab7-5ffe-b88d-2d06826cdd43
-- title:
--   Principality at a thickness-one crossing over a DVR
-- statement:
--   Let $R$ be a Noetherian local commutative ring, let $S_1$ be a domain which is a discrete valuation ring and let $S_2$ be a domain. Given ring homomorphisms $f_1 \colon R \to S_1$, assumed surjective, and $f_2 \colon R \to S_2$, elements $t, s, \varpi \in R$ and a unit $w \in R^\times$, assume that $\ker f_1 = (t)$, that $\ker f_2 = (s)$, that $t \notin (s)$, that $ts = \varpi w$, and that $\varpi$ is a non-zero-divisor of $R$. Let $P \subseteq R$ be an ideal which is saturated with respect to $\varpi$, in the sense that $\varpi r \in P$ implies $r \in P$ for all $r \in R$, and which is contained neither in $(t)$ nor in $(s)$. Then there exists $\pi \in R$ such that $P = (\pi)$, such that $\pi$ is a non-zero-divisor of $R$, and such that $\pi$ is a non-zero-divisor modulo each of the three ideals $(t)$, $(s)$ and $(ts)$, i.e. for $r \in R$, each of $\pi r \in (t)$, $\pi r \in (s)$, $\pi r \in (ts)$ implies respectively $r \in (t)$, $r \in (s)$, $r \in (ts)$.
--
--   This is the local algebra at a crossing point of thickness one ($ts = \varpi \cdot \mathrm{unit}$) in a model over a discrete valuation ring with uniformiser $\varpi$: $P$ is the germ of the closure of an effective divisor of the generic fibre, automatically $\varpi$-saturated, and $(t)$, $(s)$ are the germs of the two branches of the special fibre, the branch $R/(t)$ being regular. It is used in the study of ideals cut out on the two-chart model of the modular curve, where the conclusion provides a local generator that remains regular on each branch and on the whole special fibre.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Ideal_exists_eq_span_singleton_and_mem_nonZeroDivisors_of_forall_mul_mem_of_surjective_of_isDiscreteValuationRing.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem Ideal.exists_eq_span_singleton_and_mem_nonZeroDivisors_of_forall_mul_mem_of_surjective_of_isDiscreteValuationRing
    {R : Type*} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    {S₁ : Type*} [CommRing S₁] [IsDomain S₁] [IsDiscreteValuationRing S₁]
    {S₂ : Type*} [CommRing S₂] [IsDomain S₂]
    (f₁ : R →+* S₁) (hf₁ : Function.Surjective f₁) (f₂ : R →+* S₂)
    (t s ϖ : R) (w : Rˣ) (hker₁ : RingHom.ker f₁ = Ideal.span {t}) (hker₂ : RingHom.ker f₂ = Ideal.span {s})
    (hts : t ∉ Ideal.span {s}) (hprod : t * s = ϖ * w) (hϖ : ϖ ∈ nonZeroDivisors R)
    (P : Ideal R) (hP : ∀ r : R, ϖ * r ∈ P → r ∈ P) (hPt : ¬ P ≤ Ideal.span {t}) (hPs : ¬ P ≤ Ideal.span {s}) :
    ∃ π : R, P = Ideal.span {π} ∧ π ∈ nonZeroDivisors R ∧
      (∀ r : R, π * r ∈ Ideal.span {t} → r ∈ Ideal.span {t}) ∧
      (∀ r : R, π * r ∈ Ideal.span {s} → r ∈ Ideal.span {s}) ∧
      (∀ r : R, π * r ∈ Ideal.span {t * s} → r ∈ Ideal.span {t * s}) := by sorry
