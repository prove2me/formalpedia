-- Prove2me | Theorems.Thm_FuchsThesis_Chernoff_eq_2_28
-- name    : FuchsThesis.Chernoff.eq_2_28
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T15:56:59.349542+00:00
-- url     : https://prove2.me/theorems/0acdbac4-0a43-4bb2-a71f-7eee2a3cb552
-- title:
--   Eq. (2.28) — $P_e(N) \le \pi_0^\alpha\pi_1^{1-\alpha} F_\alpha^N \le F_\alpha^N$ for every $\alpha \in [0,1]$
-- statement:
--   Let $p_0, p_1$ be probability distributions on a finite outcome set $\{1,\dots,n\}$, $\pi_0, \pi_1 \ge 0$ priors with $\pi_0 + \pi_1 = 1$, and $N \ge 0$ the number of samplings. For any $\alpha \in [0,1]$,
--
--   $$
--   \begin{aligned}
--   P_e(N) &\le \pi_0^{\alpha}\pi_1^{1-\alpha} \sum_{b_1\dots b_N} p_0(b_1\dots b_N)^{\alpha}\, p_1(b_1\dots b_N)^{1-\alpha} \\
--   &= \pi_0^{\alpha}\pi_1^{1-\alpha} \sum_{b_1\dots b_N} \prod_{k=1}^{N} p_0(b_k)^{\alpha} p_1(b_k)^{1-\alpha} \\
--   &= \pi_0^{\alpha}\pi_1^{1-\alpha} \prod_{k=1}^{N} \sum_{b_k=1}^{n} p_0(b_k)^{\alpha} p_1(b_k)^{1-\alpha} \\
--   &= \pi_0^{\alpha}\pi_1^{1-\alpha} \Bigl(\sum_{b=1}^{n} p_0(b)^{\alpha} p_1(b)^{1-\alpha}\Bigr)^{N} \\
--   &\le \Bigl(\sum_{b=1}^{n} p_0(b)^{\alpha} p_1(b)^{1-\alpha}\Bigr)^{N},
--   \end{aligned}
--   $$
--
--   where $P_e(N)$ is the Bayes error after $N$ samplings and $p_i(b_1\dots b_N) = \prod_k p_i(b_k)$. Minimizing the right-hand side over $\alpha$ gives the first part of the Chernoff bound, $P_e(N) \le \lambda^N$.
--
--   **Formalization Note** Each link of the chain is a separate conjunct; in the three equalities the common factor $\pi_0^\alpha \pi_1^{1-\alpha}$ is cancelled.
--
--   Differences from the source:
--   - reading: first two lines of (2.28) print min{π0p0(b1…bN), π0p0(b1…bN)} and p0(b1…bN)^α p0(b1…bN)^{1−α} → min{π0p0(b1…bN), π1p1(b1…bN)} and p0(b1…bN)^α p1(b1…bN)^{1−α}; reason: misprints; the third line of (2.28), (2.21)–(2.22) and (2.11) fix the intended π1p1 and p1
--   - encoding: equalities c·S1 = c·S2 = c·S3 = c·F^N with c = π0^α π1^{1−α} → S1 = S2, S2 = S3, S3 = F^N (common factor c cancelled); reason: the cancelled equalities imply the printed ones for every c; same content
--   - encoding: outcome set {1, …, n} → arbitrary finite type B; reason: every finite set is in bijection with some {1, …, n}, and IsDist forces it to be nonempty; no instance changes
--   - encoding: strings b1…bN with trials k = 1, …, N → functions s : Fin N → B with trials indexed from 0; reason: the same finite set of strings; no instance changes
--   - reading: (2.21) prints p1(bN) as the last factor of p0(b1…bN) → productDist p0 N s = ∏ k, p0 (s k); reason: misprint; (2.21) is meant to be the product of the p0(bk), as the third line of (2.28) confirms
--   - reading: p(b)^α with p(b) = 0 at α ∈ {0, 1}, not specified by the source ((2.23) is stated for positive numbers only) → Real.rpow, with 0^0 = 1; reason: the only convention that matters at the endpoints; every link of the chain holds under it, and for α ∈ (0, 1) no convention is involved
-- source:
--   Fuchs, Distinguishability and Accessible Information in Quantum Theory, arXiv:quant-ph/9601020v1, §2.2.2, eq. (2.28), p.17 (PDF p.26)

import Mathlib
import Definitions.Def_CalibratedCE_Forecast_IsDist
import Definitions.Def_FuchsThesis_Chernoff_productDist
import Definitions.Def_FuchsThesis_Chernoff_errorProbN
import Definitions.Def_FuchsThesis_Chernoff_renyiOverlap

open CalibratedCE.Forecast

namespace FuchsThesis.Chernoff

/-- Fuchs, *Distinguishability and Accessible Information in Quantum Theory*,
arXiv:quant-ph/9601020v1, §2.2.2, eq. (2.28), p.17 (PDF p.26): for any `α ∈ [0, 1]`,
```
Pe(N) ≤ π0^α π1^{1−α} ∑_{b1…bN} p0(b1…bN)^α p1(b1…bN)^{1−α}
      = π0^α π1^{1−α} ∑_{b1…bN} ∏_{k=1}^{N} p0(bk)^α p1(bk)^{1−α}
      = π0^α π1^{1−α} ∏_{k=1}^{N} ∑_{bk=1}^{n} p0(bk)^α p1(bk)^{1−α}
      = π0^α π1^{1−α} (∑_{b=1}^{n} p0(b)^α p1(b)^{1−α})^N
      ≤ (∑_{b=1}^{n} p0(b)^α p1(b)^{1−α})^N.
```

**Formalization Note.** Each link of the printed chain is one conjunct (the common factor
`π0^α π1^{1−α}` is cancelled in the three equalities). The first two lines of (2.28) print
`π0 p0(b1…bN)` as the second argument of the min and `p0(b1…bN)^{1−α}` as the second factor; the
intended `π1 p1` and `p1` are stated (the third line and (2.21)–(2.22) fix them). Real powers are
`Real.rpow`. -/
theorem eq_2_28 {B : Type} [Fintype B] (π0 π1 : ℝ) (p0 p1 : B → ℝ)
    (hp0 : IsDist p0) (hp1 : IsDist p1) (hπ0 : 0 ≤ π0) (hπ1 : 0 ≤ π1) (hπ : π0 + π1 = 1)
    (α : ℝ) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (N : ℕ) :
    errorProbN π0 π1 p0 p1 N ≤
        π0 ^ α * π1 ^ (1 - α) *
          ∑ s : Fin N → B, productDist p0 N s ^ α * productDist p1 N s ^ (1 - α) ∧
      ∑ s : Fin N → B, productDist p0 N s ^ α * productDist p1 N s ^ (1 - α) =
        ∑ s : Fin N → B, ∏ k, p0 (s k) ^ α * p1 (s k) ^ (1 - α) ∧
      ∑ s : Fin N → B, ∏ k, p0 (s k) ^ α * p1 (s k) ^ (1 - α) =
        ∏ _k : Fin N, ∑ b, p0 b ^ α * p1 b ^ (1 - α) ∧
      ∏ _k : Fin N, ∑ b, p0 b ^ α * p1 b ^ (1 - α) = renyiOverlap p0 p1 α ^ N ∧
      π0 ^ α * π1 ^ (1 - α) * renyiOverlap p0 p1 α ^ N ≤ renyiOverlap p0 p1 α ^ N := by sorry

end FuchsThesis.Chernoff
