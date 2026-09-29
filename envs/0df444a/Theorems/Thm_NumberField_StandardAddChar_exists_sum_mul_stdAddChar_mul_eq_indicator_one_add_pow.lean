-- Prove2me | Theorems.Thm_NumberField_StandardAddChar_exists_sum_mul_stdAddChar_mul_eq_indicator_one_add_pow
-- name    : NumberField.StandardAddChar.exists_sum_mul_stdAddChar_mul_eq_indicator_one_add_pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:57.351487+00:00
-- url     : https://prove2.me/theorems/8896f870-3abd-5d32-b18c-7b63b8af3bd2
-- title:
--   Indicator of 1+mathfrak pᵥⁿ as a finite character sum
-- statement:
--   Let $K$ be a number field, let $v$ be a height-one prime of the ring of integers $\mathcal O_K$, and let $m,n$ be natural numbers with $n>0$. Then there exist a natural number $r$, adeles $y_0,\dots,y_{r-1} \in \mathbb A_K$ and complex scalars $c_0,\dots,c_{r-1}$ with the following two properties. First, each $y_i$ has vanishing archimedean component, $(y_i)_\infty = 0$, and finite component supported at $v$, i.e. $(y_i)_{v'} = 0$ for every height-one prime $v' \neq v$. Second, for every adele $a \in \mathbb A_K$ whose component at $v$ satisfies $\mathrm{v}(a_v) \le \mathrm{ofAdd}(m)$, that is $a_v \in \mathfrak p_v^{-m}$, one has $$\sum_{i<r} c_i\, \psi_K(a\,y_i) = \begin{cases} 1 & \text{if } \mathrm{v}(a_v-1) \le \mathrm{ofAdd}(-n),\ \text{i.e. } a_v \in 1+\mathfrak p_v^{n},\\ 0 & \text{otherwise,}\end{cases}$$ where $\psi_K =$ `stdAddChar K` is the standard additive character of $\mathbb A_K$, namely the standard additive character of the adeles of $\mathbb Q$ composed with the adelic trace homomorphism attached to `adelicTraceData K`. Nothing is asserted for adeles $a$ with $a_v \notin \mathfrak p_v^{-m}$.
--
--   This is finite Fourier inversion at a single finite place: on the finite quotient $\mathfrak p_v^{-m}/\mathfrak p_v^{n}$ the indicator function of the coset $1+\mathfrak p_v^{n}$ is expanded in the characters $a \mapsto \psi_K(ay)$ with $y$ supported at $v$. It is used in the unipotent surgery lemmas, where such right translates multiply a Whittaker coefficient by exactly these characters, to cut a torus variable down to principal units at a given place.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_NumberField_StandardAddChar_exists_sum_mul_stdAddChar_mul_eq_indicator_one_add_pow.lean

import Definitions.Def_NumberField_AdelicTraceFin
import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField IsDedekindDomain

theorem NumberField.StandardAddChar.exists_sum_mul_stdAddChar_mul_eq_indicator_one_add_pow
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) (m n : ℕ) (hn : 0 < n) :
    ∃ (r : ℕ) (y : Fin r → AdeleRing (𝓞 K) K) (c : Fin r → ℂ),
      (∀ i, (y i).1 = 0 ∧ ∀ v' : HeightOneSpectrum (𝓞 K), v' ≠ v → (y i).2 v' = 0) ∧
      ∀ a : AdeleRing (𝓞 K) K,
        Valued.v (a.2 v) ≤ ((Multiplicative.ofAdd (m : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) →
        (∑ i, c i * NumberField.StandardAddChar.stdAddChar K (a * y i)) =
          if Valued.v (a.2 v - 1) ≤
              ((Multiplicative.ofAdd (-(n : ℤ)) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))
          then 1 else 0 := by sorry
