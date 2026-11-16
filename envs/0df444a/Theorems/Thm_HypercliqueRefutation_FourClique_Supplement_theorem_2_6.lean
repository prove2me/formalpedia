-- Prove2me | Theorems.Thm_HypercliqueRefutation_FourClique_Supplement_theorem_2_6
-- name    : HypercliqueRefutation.FourClique.Supplement.theorem_2_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T09:27:02.480544+00:00
-- url     : https://prove2.me/theorems/36eb866b-1102-4559-9607-0e8026617c39
-- title:
--   Theorem 2.6 — costed reduction to one rectangular product
-- statement:
--   There are fixed deterministic programs for coefficient generation, left and right operand construction, and recovery, with uniform positive constants $C,d,e$, chosen before sizes, scalar fields and inputs. For every nonnegative $m,k$ with $8\mid m$ and $k$ even, they construct sparse signed coefficients and rational weights with a positive common denominator, the symmetrized cancellation identity, and polynomial-in-$m$ bit lengths. Coefficients are computed from $m,k$, never promised as input.
--
--   Write $n_A=2^{m/2}$, $n_B=\binom mk$ and $L=n_A\sum_{i=0}^{k/2}\binom mi$. For any nonnegative $n$ and arbitrary scalar matrix families, the two constructors produce
--
--   $$
--   \widehat A[(x,\ell),(z,b)]=\sum_a h^{(\ell)}_{a,b}A_a[x,z],\qquad
--   \widehat B[(z,b),y]=B_b[z,y].
--   $$
--
--   Thus a single ordinary product has dimensions $(nL\times nn_B)(nn_B\times n)$. Its entries are $P^{(\ell)}[x,y]$. The left constructor has no $B$ input. Recovery computes the weighted trace from these $n^2L$ outputs. If both input families are symmetric, then
--
--   $$
--   \sum_{x,y,\ell} w^{(\ell)}P^{(\ell)}[x,y]P^{(\ell)}[y,x]
--   =\sum_{x,y,z,z',a,b}A_a[x,z]B_b[z,y]A_a[y,z']B_b[z',x].
--   $$
--
--   Let $S=2+n+m+k+n_A+n_B+L$. All soft bounds mean a fixed uniform power of $1+\lfloor\log_2 S\rfloor$. Coefficient generation costs $\widetilde O(1+n_BL)$; dense left and right preparation cost $\widetilde O(1+n^2Ln_B)$ and $\widetilde O(1+n^2n_B)$; recovery costs $\widetilde O(1+n^2L)$. Coefficient preparation and operand generation are charged within the product stage. For any actual ordinary multiplication program taking charged time $T$ on these operands, the staged computation has the sum of these four budgets and $T$ plus 16 fixed driver units as its total bound, and returns the exact alternating contraction. The theorem neither assumes a fast multiplication program nor assigns a cost to an uncosted function.
--
--   All ordered walk indices, including coincidences, occur. No condition $k\le m$, positivity of $n$, or nonnegative/Boolean entries is required. When $k>m$ there are no B colors and the contraction is zero. This is the complete reduction interface for the source theorem; the coefficient construction remains a proof obligation inside the theorem.
--
--   Differences from the source:
--   - reading: unspecified scalar arrays and arithmetic time → arbitrary characteristic-zero scalar fields, with a single rational-code program tuple interpreted in each field; reason: the symmetrized rational-weight construction requires division by nonzero integers; no Boolean or sign restriction is placed on inputs
--   - encoding: one rectangular product and soft-O(n²L) additional work → charged coefficient generation, dense operand preparation, one ordinary multiplication execution, and soft-O(n²L) recovery; S=2+n+m+k+n_A+n_B+L with fixed uniform C,d and an independently chosen word-bound degree e; reason: the proof gives soft-O(1) entry evaluation; explicitly writing n²Ln_B entries belongs to the product stage rather than recovery, and the five execution costs are added
--   - encoding: asymptotic costs and polynomial-in-m-bit rational weights → budgets C(1+volume)(1+floor(log₂S))^d, positive common denominator and C(m+1)^d bit bounds, with bounded-word execution of independent degree e; reason: the additive ones express constant overhead at zero sizes; all nonempty source instances and asymptotic rates are retained
--   - generalization: operand construction and recovery for the symmetric input instance → constructors work on all matrix families and recovery on every product-shaped matrix; equality to the alternating contraction still requires both families symmetric; reason: the formulas and recovery procedure have these broader domains, specializing to every source instance
-- source:
--   Timothy M. Chan, Reina Itakura, Zhiyuan Ma, Yuancheng Yu, The 3-Uniform Hyperclique Hypothesis is False, STOC 2027 submission #1431 (October 2026); Theorem 2.6, printed/PDF p.5; Problem 2.2, p.3; construction in Lemma 2.4, pp.4,6-7.

import Definitions.Def_HypercliqueRefutation_FourClique_Supplement_OneProduct

set_option autoImplicit false

namespace HypercliqueRefutation.FourClique.Supplement

/-- Chan--Itakura--Ma--Yu, STOC 2027 submission #1431 (October 2026),
    Theorem 2.6, p.5, with Problem 2.2, p.3 and Lemma 2.4, pp.4,6--7.
    The dense operands are prepared in the charged product stage. Only recovery
    has the additional soft-O(n^2 L) bound. No coefficient family is an input promise. -/
theorem theorem_2_6 :
    ∃ (C d e : ℕ) (gen left right recover : ScalarMachine.Program), 0 < C ∧ 0 < d ∧ 0 < e ∧
    ∀ (m k : ℕ), 8 ∣ m → Even k →
      ∃ D : SparseData m k,
        coefficientSpec C d D ∧
        ScalarMachine.Runs (K := ℚ) gen [m,k] []
          (coefficientBudget C d m k) (ScalarMachine.wordBound (scale 0 m k) e)
          [] (coefficientCells D) ∧
        ∀ (K : Type) [Field K] [CharZero K] (n : ℕ)
          (A : Family K n (aSize m)) (B : Family K n (bSize m k)),
          let LA := leftOperand (sparseH (K := K) D) A
          let RB := rightOperand B
          let P := LA * RB
          ScalarMachine.Runs left (reductionHeader n D) (familyCells A)
            (leftBudget C d n m k) (ScalarMachine.wordBound (scale n m k) e) (leftCells LA) ∧
          ScalarMachine.Runs right [n,m,k] (familyCells B)
            (rightBudget C d n m k) (ScalarMachine.wordBound (scale n m k) e) (rightCells RB) ∧
          (∀ P' : Matrix (Fin n × Fin (layers m k)) (Fin n) K,
            ScalarMachine.Runs recover (reductionHeader n D) (productCells P')
              (recoveryBudget C d n m k) (ScalarMachine.wordBound (scale n m k) e)
              [recoveryValue D P']) ∧
          (∀ x y l, P (x,l) y = weightedProduct (sparseH D) A B l x y) ∧
          ((∀ a, (A a).IsSymm) → (∀ b, (B b).IsSymm) →
            recoveryValue D P = weightedTrace (sparseH D) (sparseW D) A B ∧
            recoveryValue D P = alternatingContraction A B ∧
            ∀ (multiply : ScalarMachine.Program) (T W : ℕ),
              ScalarMachine.Runs multiply [n * layers m k, n * bSize m k, n]
                (leftCells LA ++ rightCells RB) T W (productCells P) →
              OneProductExecution gen left right multiply recover D A B
                (16 + coefficientBudget C d m k + leftBudget C d n m k +
                  rightBudget C d n m k + T + recoveryBudget C d n m k)
                (alternatingContraction A B)) := by sorry

end HypercliqueRefutation.FourClique.Supplement
