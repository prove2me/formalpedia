-- Prove2me | Theorems.Thm_MeanCertificates1424_Hardness_Supplement_theorem_7_1
-- name    : MeanCertificates1424.Hardness.Supplement.theorem_7_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T09:07:19.811956+00:00
-- url     : https://prove2.me/theorems/e372fe30-019b-4b45-bfe1-028987a3b3b3
-- title:
--   Theorem 7.1 — doubling the budget
-- statement:
--   Fix $G$, $L$, $\epsilon$, $b$ and exact audits $Q$, and put $\bar b=\min\{2b,n\}$. Let $u^{(\bar b)}_Q(0)$ be the upper endpoint of the certificate for the zero report, zero audit values and budget $\bar b$. Then, in the extended reals,
--   $$R^*_Q(G,b,L,\epsilon)=u^{(\bar b)}_Q(0),$$
--   and this certificate is symmetric about $0$. Consequently any algorithm for observed certificates, run with budget $\bar b$, computes the worst-case radius; on trees this costs $O(n(\bar b+1)(\min\{\bar b,n-\bar b\}+1))$ operations.
--
--   **Formalization Note** The tree program reads $G,b,L,\epsilon,Q$ and reports whether the radius is finite and, if so, its value.
--
--   Differences from the source:
--   - encoding: O(·) arithmetic operations (and space) → one fixed program of the unit-cost real RAM and one constant C>0 chosen before every instance, every executed instruction charged, space = distinct cells accessed; reason: the paper's model counts exact arithmetic operations and comparisons; charging all instructions only strengthens the bound
--   - reading: In the noiseless case, Theorem 7.2 gives a direct integer-alphabet implementation → not restated here; reason: a pointer to Theorem 7.2, which is its own item
-- source:
--   chaomeng chen, Junhao Dong, STOC 2027 submission #1424 (October 2026), Theorem 7.1, printed p.21 (PDF p.23)

import Mathlib
import Definitions.Def_MeanCertificates1424_Hardness_Supplement_RAM

set_option autoImplicit false

open MeanCertificates1424.Hardness

namespace MeanCertificates1424.Hardness.Supplement

/-- Theorem 7.1, printed p.21 / PDF p.23. With `b̄ = min{2b, n}`, in the extended reals
`R*_Q(G, b, L, ε) = u_Q^{(b̄)}(0)`, the upper endpoint for the zero report, zero audit values and
budget `b̄`, and that certificate is symmetric about `0`. On trees one fixed program computes the
radius (`I[0] = 1` iff finite, then `R[0] = R*_Q`) within `C n (b̄ + 1)(min{b̄, n − b̄} + 1)`
operations; its input is `G, b, L, ε, Q`. -/
theorem theorem_7_1 :
    (∀ {n : ℕ} (G : SimpleGraph (Fin n)) (b : ℕ) (L ε : ℝ) (Q : Finset (Fin n)),
      1 ≤ n → G.Connected → 0 < L → 0 ≤ ε → b ≤ n →
      ((minimaxRadius G b L ε Q (uniformW n) : ENNReal) : EReal) =
          upper (exactInst G (min (2 * b) n) L ε Q (uniformW n) 0 0) ∧
        lower (exactInst G (min (2 * b) n) L ε Q (uniformW n) 0 0) =
          -upper (exactInst G (min (2 * b) n) L ε Q (uniformW n) 0 0) ∧
        ∀ x ∈ CI (exactInst G (min (2 * b) n) L ε Q (uniformW n) 0 0),
          -x ∈ CI (exactInst G (min (2 * b) n) L ε Q (uniformW n) 0 0)) ∧
    ∃ (P : Program) (C : ℕ), 0 < C ∧
      ∀ {n : ℕ} (G : SimpleGraph (Fin n)) (b : ℕ) (L ε : ℝ) (Q : Finset (Fin n)),
        1 ≤ n → G.IsTree → 0 < L → 0 ≤ ε → b ≤ n →
        ∃ fin, RunsWithin P (fun _ _ => 0)
            (encInst (exactInst G b L ε Q (uniformW n) 0 0)).1
            (encInst (exactInst G b L ε Q (uniformW n) 0 0)).2
            (C * n * (min (2 * b) n + 1) * (min (min (2 * b) n) (n - min (2 * b) n) + 1))
            (3 * (C * n * (min (2 * b) n + 1) * (min (min (2 * b) n) (n - min (2 * b) n) + 1)))
            fin ∧
          (fin.imem 0 = 1 ↔ minimaxRadius G b L ε Q (uniformW n) ≠ ⊤) ∧
          (minimaxRadius G b L ε Q (uniformW n) ≠ ⊤ →
            0 ≤ fin.rmem 0 ∧ ENNReal.ofReal (fin.rmem 0) = minimaxRadius G b L ε Q (uniformW n))
    := by sorry

end MeanCertificates1424.Hardness.Supplement
