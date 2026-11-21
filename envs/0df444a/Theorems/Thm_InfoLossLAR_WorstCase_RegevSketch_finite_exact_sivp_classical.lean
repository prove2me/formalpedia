-- Prove2me | Theorems.Thm_InfoLossLAR_WorstCase_RegevSketch_finite_exact_sivp_classical
-- name    : InfoLossLAR.WorstCase.RegevSketch.finite_exact_sivp_classical
-- status  : Proved
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-15T08:57:52.654193+00:00
-- url     : https://prove2.me/theorems/aa77887f-46d8-4d0f-827a-8244cc17bc2a
-- title:
--   Classical exact SIVP below a fixed dimension cutoff
-- statement:
--   Fix a natural-number cutoff $N_0$. There exists a deterministic polynomial-time function on binary strings which, for every nonsingular integer basis $B$ in dimension $1\le n<N_0$, outputs a string beginning with an encoding of $n$ independent lattice vectors $v_1,\ldots,v_n$ such that
--
--   $$
--   \max_i\|v_i\|_2\le\lambda_n(L(B)).
--   $$
--
--   The running-time polynomial may depend on $N_0$, but the input basis entries may have arbitrary finite binary length. The function is total on all binary strings; only valid nonsingular basis encodings are required to satisfy the output condition. The statement isolates the classical lattice-algorithm obligation used in the finite-dimensional patch.
--
--   **Formalization Note.** The underlying time predicate uses the platform's multi-stack Turing machine. The output encodes vectors in ambient coordinates. The exact SIVP algorithm and the fixed-dimension input-length adaptation are motivated by Micciancio and Voulgaris; matching their algorithms to this particular machine and encoding is part of this open obligation.
-- source:
--   Daniele Micciancio and Panagiotis Voulgaris, A deterministic single exponential time algorithm for most lattice problems based on Voronoi cell computations, https://cseweb.ucsd.edu/~daniele/papers/Voronoi.pdf, pp. 6 and 8, §2 and Corollary 3.3. The explicit TM2/encoding and arbitrary bit-length adaptations are part of the formalization obligation, not claimed verbatim.

import Definitions.Def_InfoLossLAR_RegevSketch_DGS

set_option autoImplicit false
open QAlgorithms.Complexity InfoLossLAR.WorstCase

namespace InfoLossLAR.WorstCase.RegevSketch

theorem finite_exact_sivp_classical (cutoff : ℕ) :
  ∃ f : Str → Str, PolyTimeComputable f ∧
    ∀ n, 1 ≤ n → n < cutoff → ∀ B : Matrix (Fin n) (Fin n) ℤ, B.det ≠ 0 →
      ∃ y : Fin n → Fin n → ℤ, encVec (encVec encI) y <+: f (encMat encI B) ∧
        (∀ i, intVecE (y i) ∈ lattice B) ∧ LinearIndependent ℝ (fun i => intVecE (y i)) ∧
        ∀ i, ‖intVecE (y i)‖ ≤ lamN B := by sorry

end InfoLossLAR.WorstCase.RegevSketch
