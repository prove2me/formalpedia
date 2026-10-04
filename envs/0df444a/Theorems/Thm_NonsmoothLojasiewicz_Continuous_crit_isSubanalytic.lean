-- Prove2me | Theorems.Thm_NonsmoothLojasiewicz_Continuous_crit_isSubanalytic
-- name    : NonsmoothLojasiewicz.Continuous.crit_isSubanalytic
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T09:14:39.52666+00:00
-- url     : https://prove2.me/theorems/99987d9b-a524-4da0-8cc2-4b7cbe110766
-- title:
--   Proposition 2.13(ii), the clause on $\mathrm{crit}\, f$: the critical set is subanalytic
-- statement:
--   Let $f : \mathbb{R}^n \to \mathbb{R} \cup \{+\infty\}$ be a subanalytic function which is **relatively bounded on its domain**: for every bounded set $B \subseteq \mathbb{R}^n$, the set of values
--   $$
--   \{f(x) : x \in \operatorname{dom} f \cap B\}
--   $$
--   is bounded. Then the set of critical points $\operatorname{crit} f = \{x : 0 \in \partial f(x)\}$ is a subanalytic subset of $\mathbb{R}^n$.
--
--   Subanalyticity of the critical set gives it a locally finite number of connected components, each subanalytically path connected; this is the structure on which the constancy of $f$ on critical components and the Łojasiewicz inequality rest.
--
--   **Formalization Note.** Relative boundedness is transcribed from Proposition 2.7 (p. 1210) as: for every bounded `B` there is `M` with `|f x| ≤ M` for all `x ∈ B` with `f x ≠ ⊤` (the real value `(f x).toReal` is the true value there since `f` never takes `⊥`). Only the clause of (ii) about $\operatorname{crit} f$ is formalized; the clauses about $\hat\partial f$, $\partial f$ and $m_f$, and part (i) on globally subanalytic functions, are not.
-- source:
--   Bolte, Daniilidis & Lewis, SIAM J. Optim. 17 (2007) 1205–1223, p. 1211 (PDF p. 7), Proposition 2.13(ii), clause on crit f; relative boundedness from Proposition 2.7, p. 1210 (PDF p. 6)

import Mathlib
import Definitions.Def_NonsmoothLojasiewicz_Continuous_IsSubanalytic
import Definitions.Def_NonsmoothLojasiewicz_Continuous_slope

open Filter Topology
open scoped ENNReal

namespace NonsmoothLojasiewicz.Continuous

/-- Proposition 2.13(ii) (p. 1211), the clause on `crit f`: if `f` is subanalytic and
relatively bounded on its domain (Proposition 2.7, p. 1210: `{f(x) : x ∈ dom f ∩ B}` is bounded
for every bounded `B ⊆ ℝⁿ`), then `crit f` is a subanalytic set. -/
theorem crit_isSubanalytic {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → EReal) (hf : ∀ x, f x ≠ ⊥)
    (hsub : IsSubanalyticFn f)
    (hrb : ∀ B : Set (EuclideanSpace ℝ (Fin n)), Bornology.IsBounded B →
      ∃ M : ℝ, ∀ x ∈ B, f x ≠ ⊤ → |(f x).toReal| ≤ M) :
    IsSubanalytic (crit f) := by sorry

end NonsmoothLojasiewicz.Continuous
