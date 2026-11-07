-- Prove2me | Theorems.Thm_GuardedSSSP_theorem_3_1
-- name    : GuardedSSSP.theorem_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:49:35.960376+00:00
-- url     : https://prove2.me/theorems/fdc8f6e6-f926-4830-b009-3b29d98b001e
-- title:
--   Theorem 3.1 — uniform near-envelope truncation $1\le f_{D_*(x)}(x)/\Phi(x)\le A_0^{2^{-D_*(x)}}\le A_0$
-- statement:
--   Let $T_4\ge16$. For every real $x\ge X_4$, with $d=D_*(x)$,
--
--   $$1\le\frac{f_d(x)}{\Phi(x)}\le A_0^{2^{-d}}\le A_0,$$
--
--   and $f_{D_*(x)}(x)/\Phi(x)\to1$ as $x\to\infty$.
--
--   At the selected depth the finite factor is within a constant factor of the envelope $\Phi$, which is how $\Phi(K)$ enters Theorem 1.1.
--
--   Differences from the source:
--   - generalization: the fixed base threshold T₄ of Specification A.1 ("a sufficiently large integer T₄ ≥ 16") → every natural T₄ ≥ 16; reason: the statement for every T₄ ≥ 16 specializes to the paper's fixed T₄
-- source:
--   Cai, Uniform Guarded Bootstrapping for Topology-Sensitive Directed Shortest Paths, STOC 2027 submission (manuscript sha256 bcda0e91…), Theorem 3.1, p.7 (PDF p.8)

import Mathlib
import Definitions.Def_GuardedSSSP_LogHierarchy
import Definitions.Def_GuardedSSSP_Thresholds

namespace GuardedSSSP

open Filter Topology

/-- **Theorem 3.1** (Uniform near-envelope truncation), p.7 (PDF p.8).

Bin Cai, *Uniform Guarded Bootstrapping for Topology-Sensitive Directed Shortest Paths*, STOC 2027
submission (manuscript sha256 bcda0e91…): "For x ≥ X₄ and d = D∗(x),
1 ≤ f_d(x)/Φ(x) ≤ A₀^{2^{−d}} ≤ A₀. (14) In particular the ratio tends to one as x → ∞."

For every base threshold `T₄ ≥ 16`: for every real `x ≥ X₄`, with `d = D*(x)`, the three inequalities of
(14) hold; and `f_{D*(x)}(x)/Φ(x) → 1` as `x → ∞`.

**Formalization Note.** `A₀ = 256(T₄ + 1)²`. The base threshold is any `T₄ ≥ 16`, which contains the
paper's fixed `T₄` (Specification A.1). -/
theorem theorem_3_1 (T4 : ℕ) (hT4 : 16 ≤ T4) :
    (∀ x : ℝ, (X4 T4 : ℝ) ≤ x →
      1 ≤ f (Dstar T4 x) x / Phi x ∧
      f (Dstar T4 x) x / Phi x ≤ A0 T4 ^ ((2 : ℝ) ^ (-(Dstar T4 x : ℝ))) ∧
      A0 T4 ^ ((2 : ℝ) ^ (-(Dstar T4 x : ℝ))) ≤ A0 T4) ∧
    Tendsto (fun x : ℝ => f (Dstar T4 x) x / Phi x) atTop (𝓝 1) := by sorry

end GuardedSSSP
