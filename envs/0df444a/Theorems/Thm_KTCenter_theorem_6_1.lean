-- Prove2me | Theorems.Thm_KTCenter_theorem_6_1
-- name    : KTCenter.theorem_6_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T11:28:27.806692+00:00
-- url     : https://prove2.me/theorems/5c2559f0-61ba-4552-bde2-8439b454f322
-- title:
--   Theorem 6.1 — deterministic simultaneous optimization within $\xi W$ in polynomial time
-- statement:
--   Fix $K\in\mathbb N$, positive rationals $C_0,C_1$ and a rational $0<\xi<1$. There is a deterministic polynomial-time algorithm (a Turing machine running in time polynomial in the binary encoding length of the instance) that, given a cost instance satisfying (7), returns $p\in\mathcal P(U)$ with
--
--   $$\max_{i\in[n]}\tilde C_i(p)\le\min_{q\in\mathcal P(U)}\max_{i\in[n]}\tilde C_i(q)+\xi W.\qquad(75)$$
--
--   This is the derandomized joint optimization that replaces Algorithm 9 in the PTAS.
--
--   Differences from the source:
--
--   - reading: "a deterministic algorithm … runs in polynomial time in the total binary encoding length" → Turing.TM2ComputableInPolyTime with input encoding encCost and output the list of key indices; reason: the paper names no machine and counts binary encoding length
--   - encoding: K, C₀, C₁, ξ fixed → parameters quantified before the machine, not inputs; reason: this is what "for fixed" says
-- source:
--   Chakraborty, Das, Mukherjee, Kendall–tau Center Admits a PTAS, STOC 2027 submission (manuscript sha256 4739ffba…), Theorem 6.1, eq. (75), p.58 (PDF p.60)

import Mathlib
import Definitions.Def_KTCenter_CostInstance
import Definitions.Def_KTCenter_encCost

namespace KTCenter

/-- **Theorem 6.1** (Deterministic simultaneous optimization), eq. (75), p.58 (PDF p.60).

Chakraborty, Das, Mukherjee, *Kendall–tau Center Admits a PTAS*, STOC 2027 submission (manuscript
sha256 4739ffba…).

**Formalization Note.** "For fixed `K, C₀, C₁, ξ`": they precede the machine and are not inputs. The
machine is a Mathlib `Turing.TM2ComputableInPolyTime`; the input encoding `encCost` writes every table
in binary. The output is the list of key indices of `p`. -/
theorem theorem_6_1 (K : ℕ) (C₀ C₁ ξ : ℚ) (hC₀ : 0 < C₀) (hC₁ : 0 < C₁) (hξ0 : 0 < ξ) (hξ1 : ξ < 1) :
    ∃ alg : CostInstance K C₀ C₁ → List ℕ,
      Nonempty (Turing.TM2ComputableInPolyTime encCost encIdx alg) ∧
      ∀ I : CostInstance K C₀ C₁, ∃ p : I.Assign,
        alg I = idxList p ∧ I.maxCost p ≤ I.minMaxCost + ξ * I.W := by sorry

end KTCenter
