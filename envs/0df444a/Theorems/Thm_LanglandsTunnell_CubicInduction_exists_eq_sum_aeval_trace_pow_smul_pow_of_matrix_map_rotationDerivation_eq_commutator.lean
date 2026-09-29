-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_exists_eq_sum_aeval_trace_pow_smul_pow_of_matrix_map_rotationDerivation_eq_commutator
-- name    : LanglandsTunnell.CubicInduction.exists_eq_sum_aeval_trace_pow_smul_pow_of_matrix_map_rotationDerivation_eq_commutator
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:04.547556+00:00
-- url     : https://prove2.me/theorems/55666963-0439-5300-9ed8-d8b57883e96e
-- title:
--   SO(3)-equivariant matrix polynomials on symmetric 3× 3 matrices
-- statement:
--   Let $P = \mathbb{C}[X_{(a,b)} : a \le b]$ be the polynomial ring over $\mathbb{C}$ on the set of pairs $(a,b) \in \mathrm{Fin}\,3 \times \mathrm{Fin}\,3$ with $a \le b$, let $Y$ be the symmetric $3\times 3$ matrix over $P$ whose $(a,b)$ entry is $X_{(a,b)}$ for $a \le b$ and $X_{(b,a)}$ otherwise, and for $i,j \in \mathrm{Fin}\,3$ let $K_{ij} = E_{ij} - E_{ji}$ be the difference of the two matrix units, viewed over $P$. Let $D_{ij}$ be the $\mathbb{C}$-derivation of $P$ determined by sending the variable indexed by $(a,b)$, $a \le b$, to the $(a,b)$ entry of the commutator $K_{ij}Y - YK_{ij}$. The theorem asserts, for every $3\times 3$ matrix $M$ with entries in $P$: if applying $D_{ij}$ to each entry of $M$ yields $K_{ij}M - MK_{ij}$ for all $i,j \in \mathrm{Fin}\,3$, then there exist polynomials $G_0, G_1, G_2 \in \mathbb{C}[T_0,T_1,T_2]$ such that $M = \sum_{n=0}^{2} G_n(\operatorname{tr} Y, \operatorname{tr} Y^2, \operatorname{tr} Y^3)\, Y^{n}$, the scalar acting entrywise.
--
--   This is the matrix-valued ($\mathrm{End}(\mathbb{C}^3)$-valued) companion of the classical description of polynomial invariants of the rotation action on symmetric $3\times 3$ matrices: the equivariant polynomial maps $\mathrm{Sym}_3 \to M_3(\mathbb{C})$ are generated over the ring of invariants by $1$, $Y$ and $Y^2$. It feeds the finiteness statement [`LanglandsTunnell.CubicInduction.mem_span_invariant_mul_of_diagCasimir_add_two_eq_zero`](thm.html#LanglandsTunnell.CubicInduction.mem_span_invariant_mul_of_diagCasimir_add_two_eq_zero) in the cubic-induction input to the Langlands–Tunnell theorem.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_exists_eq_sum_aeval_trace_pow_smul_pow_of_matrix_map_rotationDerivation_eq_commutator.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_KFinite3
import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem LanglandsTunnell.CubicInduction.exists_eq_sum_aeval_trace_pow_smul_pow_of_matrix_map_rotationDerivation_eq_commutator
    (M : Matrix (Fin 3) (Fin 3) (MvPolynomial {ij : Fin 3 × Fin 3 // ij.1 ≤ ij.2} ℂ)) :
    let Y : Matrix (Fin 3) (Fin 3) (MvPolynomial {ij : Fin 3 × Fin 3 // ij.1 ≤ ij.2} ℂ) :=
      Matrix.of fun a b => if h : a ≤ b then MvPolynomial.X ⟨(a, b), h⟩ else MvPolynomial.X ⟨(b, a), le_of_not_ge h⟩
    let K : Fin 3 → Fin 3 → Matrix (Fin 3) (Fin 3) (MvPolynomial {ij : Fin 3 × Fin 3 // ij.1 ≤ ij.2} ℂ) :=
      fun i j => Matrix.single i j 1 - Matrix.single j i 1
    let D : Fin 3 → Fin 3 →
        Derivation ℂ (MvPolynomial {ij : Fin 3 × Fin 3 // ij.1 ≤ ij.2} ℂ)
          (MvPolynomial {ij : Fin 3 × Fin 3 // ij.1 ≤ ij.2} ℂ) :=
      fun i j => MvPolynomial.mkDerivation ℂ fun v => (K i j * Y - Y * K i j) v.1.1 v.1.2
    (∀ i j : Fin 3, M.map (D i j) = K i j * M - M * K i j) →
      ∃ G : Fin 3 → MvPolynomial (Fin 3) ℂ,
        M = ∑ n : Fin 3,
          MvPolynomial.aeval (fun m : Fin 3 => (Y ^ ((m : ℕ) + 1)).trace) (G n) • Y ^ (n : ℕ) := by sorry
