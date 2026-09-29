-- Prove2me | Theorems.Thm_MvFormalGroup_smul_logCoeff_eq_sum_mul_map_iterate_of_smul_logCoeff_eq_sum_map_iterate_mul
-- name    : MvFormalGroup.smul_logCoeff_eq_sum_mul_map_iterate_of_smul_logCoeff_eq_sum_map_iterate_mul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.856965+00:00
-- url     : https://prove2.me/theorems/1faf8375-a1d5-5c9c-b7dd-f99268c04076
-- title:
--   Last-factor form of the logarithm recursion over ℚₚ
-- statement:
--   Fix a prime $p$ and an integer $d \ge 0$, and let $R = \mathbb{Q}_p[X_{(m,i,j)}]$ be the polynomial ring `MvPolynomial (ℕ × Fin d × Fin d) (Padic p)` on variables indexed by triples $(m,i,j)$ with $m \in \mathbb{N}$ and $i,j \in \mathrm{Fin}\,d$. Write $\sigma$ for the $\mathbb{Q}_p$-algebra endomorphism of $R$ sending each variable $X_v$ to $X_v^p$ (the map `MvPolynomial.aeval fun v => MvPolynomial.X v ^ p`), acting on matrices entrywise through `Matrix.map`, and let $X^{(m)} = (X_{(m,i,j)})_{i,j}$ denote the $m$-th $d \times d$ matrix of variables. Let $a : \mathbb{N} \to \mathrm{Mat}_{d \times d}(R)$ be a sequence of matrices with $a_0$ the identity matrix and satisfying, for every $k \in \mathbb{N}$, the first-factor recursion $p \cdot a_{k+1} = \sum_{m=0}^{k} X^{(m)} \, \sigma^{m+1}(a_{k-m})$, the scalar $p$ acting on the matrix entrywise. Then for every $n \in \mathbb{N}$ the same sequence satisfies the last-factor recursion $$p \cdot a_{n+1} = \sum_{m=0}^{n} a_{n-m} \, \sigma^{\,n-m}\bigl(X^{(m)}\bigr).$$
--
--   The matrices $a_k$ are the coefficients of the logarithm of the universal $d$-dimensional $p$-typical formal group law in Hazewinkel's functional-equation setting, and the two recursions correspond to peeling off the first, respectively the last, variable matrix from the explicit solution. The equivalence is used in the construction of a $V$-basis for the associated Cartier module, through [`MvFormalGroup.exists_cartierModule_vBasis_mvPolynomial_X_of_log`](thm.html#MvFormalGroup.exists_cartierModule_vBasis_mvPolynomial_X_of_log).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MvFormalGroup_smul_logCoeff_eq_sum_mul_map_iterate_of_smul_logCoeff_eq_sum_map_iterate_mul.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

theorem MvFormalGroup.smul_logCoeff_eq_sum_mul_map_iterate_of_smul_logCoeff_eq_sum_map_iterate_mul
    (p : ℕ) [Fact p.Prime] (d : ℕ)
    (a : ℕ → Matrix (Fin d) (Fin d) (MvPolynomial (ℕ × Fin d × Fin d) (Padic p)))
    (h1 : a 0 = 1)
    (h2 : ∀ k : ℕ, (p : MvPolynomial (ℕ × Fin d × Fin d) (Padic p)) • a (k + 1)
      = ∑ m ∈ Finset.range (k + 1),
          (Matrix.of fun i j => MvPolynomial.X (m, i, j)) *
            (a (k - m)).map (⇑(MvPolynomial.aeval fun v => MvPolynomial.X v ^ p))^[m + 1])
    (n : ℕ) :
    (p : MvPolynomial (ℕ × Fin d × Fin d) (Padic p)) • a (n + 1)
      = ∑ m ∈ Finset.range (n + 1),
          a (n - m) * (Matrix.of fun i j => (MvPolynomial.X (m, i, j) :
            MvPolynomial (ℕ × Fin d × Fin d) (Padic p))).map
              (⇑(MvPolynomial.aeval fun v =>
                (MvPolynomial.X v : MvPolynomial (ℕ × Fin d × Fin d) (Padic p)) ^ p))^[n - m] := by sorry
