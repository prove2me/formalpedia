-- Prove2me | Theorems.Thm_MonoidProdQ_Supplement_theorem_58
-- name    : MonoidProdQ.Supplement.theorem_58
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T11:24:39.649733+00:00
-- url     : https://prove2.me/theorems/fbaffe5f-3427-4545-b688-1cdec6cf455c
-- title:
--   Theorem 58 — quantitative AGS bound $Q_{1/3}\le\min\{n,\sqrt n((|M|+1)\log(n+2))^{O(D_J(M)+1)}\}$
-- statement:
--   There is an absolute constant $C$ such that for every finite aperiodic monoid $M$ and every $n\ge1$,
--   $$Q_{1/3}(\mathrm{Prod}_{M,n})\le\min\Bigl\{n,\ \sqrt n\,\bigl((|M|+1)\log(n+2)\bigr)^{C(D_J(M)+1)}\Bigr\},$$
--   where $D_J(M)$ is the two-sided ideal depth. This makes the dependence of the Aaronson–Grier–Schaeffer bound on $|M|$ and on the ideal structure explicit.
--
--   **Formalization Note** $\log$ is natural; the power is a real power.
--
--   Differences from the source:
--
--   - encoding: an exponent O(D_J(M) + 1) with absolute implicit constant → exponent C·(D_J(M) + 1) with ∃ C > 0 chosen before M and n; reason: the base (|M| + 1) log(n + 2) exceeds 1, so the two forms are equivalent
--   - encoding: n ≥ 1 input positions (standing assumption, p.21) → 1 ≤ n as a hypothesis; reason: with no position the platform's query register is empty and Q_{1/3} is the undefined value ⊤
-- source:
--   Lee–Santha, The quantum query complexity of the semigroup product problem, arXiv:2609.39974 (held version, sha256 9eec405d…ffb6), Theorem 58, p.75

import Definitions.Def_MonoidProdQ_IsAperiodic
import Definitions.Def_MonoidProdQ_prodMap
import Definitions.Def_MonoidProdQ_Q13
import Definitions.Def_MonoidProdQ_Supplement_twoSidedIdealDepth

open scoped ENNReal

universe u

namespace MonoidProdQ.Supplement

/-- Lee–Santha, *The quantum query complexity of the semigroup product problem*,
arXiv:2609.39974 (held version, sha256 9eec405d…ffb6), Theorem 58, p.75: "Let M be a finite
aperiodic monoid. For every n ≥ 1, Q_{1/3}(Prod_{M,n}) ≤ min{n, √n ((|M| + 1) log(n + 2))^{O(D_J(M)+1)}}.
The implicit constant in the exponent is absolute." One absolute `C > 0`, chosen before `M` and
`n`, with `Q_{1/3}(Prod_{M,n}) ≤ min{n, √n ((|M| + 1) log(n + 2))^{C(D_J(M)+1)}}`.

**Formalization Note.** `D_J(M)` is `twoSidedIdealDepth M`; `log` is natural (Conventions,
p.23); the power is a real power. Its base `(|M| + 1) log(n + 2) ≥ 2 log 3 > 1`, so an exponent
`O(D_J(M) + 1)` is the same as an exponent exactly `C(D_J(M) + 1)`. `Prod_{M,n}` is
`prodMap univ n` on all of `Mⁿ`. -/
theorem theorem_58 :
    ∃ C : ℝ, 0 < C ∧
      ∀ (M : Type u) [Monoid M] [Fintype M] [DecidableEq M], IsAperiodic M →
        ∀ n : ℕ, 1 ≤ n →
          (Q13 (prodMap (Finset.univ : Finset M) n) Finset.univ : ℝ≥0∞) ≤
            ENNReal.ofReal (min (n : ℝ) (Real.sqrt n *
              ((Fintype.card M + 1) * Real.log (n + 2)) ^ (C * (twoSidedIdealDepth M + 1)))) := by sorry

end MonoidProdQ.Supplement
