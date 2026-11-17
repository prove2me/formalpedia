-- Prove2me | Theorems.Thm_HoneycombCodes_Supplement_theorem_10_2
-- name    : HoneycombCodes.Supplement.theorem_10_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T06:40:28.454961+00:00
-- url     : https://prove2.me/theorems/16fec6bf-1c4e-46f8-9a23-dde9bd0f44ce
-- title:
--   Theorem 10.2 — two-axis hierarchy is sound, monotone in $r$ and $t$, and $\mathrm{HC}_{r,t}(n,d)=A_2(n,d)$ for $t\ge A_2(n,d)$
-- statement:
--   Let $n\ge1$, $d\ge0$ and $\alpha=A_2(n,d)$. For all $r\ge1$ and $t\ge0$,
--
--   $$
--   \alpha\le\mathrm{HC}_{r,t}(n,d),\qquad \mathrm{HC}_{r+1,t}(n,d)\le\mathrm{HC}_{r,t}(n,d),\qquad \mathrm{HC}_{r,t+1}(n,d)\le\mathrm{HC}_{r,t}(n,d),
--   $$
--
--   and
--
--   $$
--   \mathrm{HC}_{r,t}(n,d)=A_2(n,d)\qquad\text{for every }t\ge A_2(n,d).
--   $$
--
--   Here $\mathrm{HC}_{r,t}$ is the seeded two-axis bound (112): the raw row bound $\mathrm{HC}^{row}_r$ for $t=0$, and for $t\ge1$ its minimum with the anchored moment relaxation $\mathrm{Mom}_{r,t}$ (Definition 10.1), which adds to the order-$t$ stable-set moment hierarchy of the forbidden-distance graph the localizers of the two quadratic certificate polynomials $Q_h$, $T_h$ of every eligible certificate $h\in\mathfrak C_r(n)$. The anchor axis recovers the exact code size at a finite level, independently of the row depth.
--
--   Differences from the source:
--
--   - encoding: all $n,d$ → $n\ge1$; reason: $s_{n,d}=1-2d/n$ is undefined at $n=0$
--   - encoding: the moment sequence indexed by codes of size at most $2t$ → a function on all finite sets of words, read through the extension by $0$ on non-codes; reason: only the values on codes of size at most $2t$ enter the constraints and the objective, so the feasible objective values are the same
--   - encoding: $\max$ in Definition 10.1 → a real `sSup` of the feasible objective values; reason: the maximum is attained (p.47)
-- source:
--   W. Gay, F. Granha Jeronimo, L. Liu, The Honeycomb Framework for Code Bounds, arXiv:2608.20287v2 (sha256 f4b07e318538a352116042dc4da0d4e9d47cfd979cf302c7fce3324584a3cd51), §10.2, Theorem 10.2, eqs. (113)–(115), p.48 (PDF 50); Definition 10.1 and (112), p.47 (PDF 49)

import Mathlib
import Definitions.Def_PrettyGoodCriterion_rateFunction
import Definitions.Def_HoneycombCodes_Supplement_HCrt

set_option autoImplicit false

namespace HoneycombCodes.Supplement

/-- **Theorem 10.2 (soundness, monotonicity and finite convergence of the two-axis hierarchy)**,
Gay, Granha Jeronimo, Liu, *The Honeycomb Framework for Code Bounds*, arXiv:2608.20287v2
(sha256 f4b07e31…cd51), p.48 (PDF 50). Let `α = A₂(n, d)`. For all `r ≥ 1` and `t ≥ 0`,
`α ≤ HC_{r,t}(n, d)` (113), `HC_{r+1,t}(n, d) ≤ HC_{r,t}(n, d)` (114),
`HC_{r,t+1}(n, d) ≤ HC_{r,t}(n, d)` (115); and `HC_{r,t}(n, d) = A₂(n, d)` for every `t ≥ A₂(n, d)`.

**Formalization Note.** `A₂` is the published `PrettyGoodCriterion.A2`; `HC_{r,t}` is (112) with the
anchored relaxation `Mom_{r,t}` of Definition 10.1 (moment variables on codes of `G_{n,d}`,
localizers of `Q_h`, `T_h` for every eligible `h ∈ C_r(n)`). `n ≥ 1` (the threshold
`s_{n,d} = 1 − 2d/n` needs it). -/
theorem theorem_10_2 (n d : ℕ) (hn : 1 ≤ n) :
    (∀ r t : ℕ, 1 ≤ r →
      (PrettyGoodCriterion.A2 n d : ℝ) ≤ HCrt r n d t ∧
        HCrt (r + 1) n d t ≤ HCrt r n d t ∧
        HCrt r n d (t + 1) ≤ HCrt r n d t) ∧
    ∀ r t : ℕ, 1 ≤ r → PrettyGoodCriterion.A2 n d ≤ t →
      HCrt r n d t = (PrettyGoodCriterion.A2 n d : ℝ) := by sorry

end HoneycombCodes.Supplement
