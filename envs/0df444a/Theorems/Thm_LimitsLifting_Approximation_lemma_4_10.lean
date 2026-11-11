-- Prove2me | Theorems.Thm_LimitsLifting_Approximation_lemma_4_10
-- name    : LimitsLifting.Approximation.lemma_4_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:38:48.646443+00:00
-- url     : https://prove2.me/theorems/b9f3ed3e-2bf4-4dd4-93a1-2a6cbe0caf0d
-- title:
--   Lemma 4.10 — simulation: a 0.96-dense member of $\mathcal M_w$ gives a width-$O(w)$ refutation
-- statement:
--   Let $F$ be an unsatisfiable CNF over $[n]$ in which every variable occurs and no clause is tautological; let $m=n^\Delta$ and let $\mathcal M_w$ be the approximation model built from a Rectangle Scheme with constant $K$.
--
--   For every sufficiently large real $\Delta$ and every $K>0$ there are $K'>0$ and $n_0$ such that for all $n\ge n_0$, every such scheme, every such $F$ and every $0<w\le n$: if some $g\in\mathcal M_w$ has a rectangle $R_g=S_g\times T_g$ with
--   $$\frac{|S_g|}{m^n}\ge 0.96\qquad\text{and}\qquad\frac{|T_g|}{2^{mn}}\ge 0.96,$$
--   then $F$ has a Resolution refutation of width at most $K'w$.
--
--   This is the simulation step of dag-like lifting: a function of the model that is dense on both sides yields a low-width Prover strategy for $F$, hence a low-width refutation.
--
--   **Formalization Note** $O(w)$ is $K'w$ with $K'$ fixed before $n$, the scheme, $F$ and $w$. A Resolution refutation is a derivation without weakening ending in the empty clause, from the published CNF definition.
--
--   Differences from the source:
--   - generalization: the Rectangle Scheme of [GGKS20] → every deterministic scheme with the properties of Lemma 4.7 (constant K); reason: the source states only these properties of the scheme ("We merely state the properties of the algorithm that we will use", printed p.20) and its proofs use only them; in M_w the scheme is applied only at gates, never to the input leaves (Definition 4.9); the [GGKS20] scheme has these properties (Lemma 4.7), so the statement specializes to the source's.
--   - encoding: m = n^Δ for a large enough constant Δ → real Δ ≥ Δ₀, with integer m and (m : ℝ) = (n : ℝ)^Δ; reason: preserves all admissible real exponents; block length is an integer, with no rounding or restriction to integer exponents.
--   - encoding: [m], [n] → Fin m, Fin n; reason: index shift, same instances.
-- source:
--   Gaia Carenini, Bruno Cavalar, Stefan Grosser, Jan Pich, Limits of Lifting, STOC 2027 submission #309 (October 2026), Lemma 4.10, printed p. 22 (PDF p. 23); proof §4.4, printed pp. 23–25 (PDF pp. 24–26)

import Mathlib
import Definitions.Def_MultiplierAssoc206_Resolution_CNF
import Definitions.Def_LimitsLifting_Approximation_ApproxModel
import Definitions.Def_LimitsLifting_Approximation_CanonicalCover
import Definitions.Def_LimitsLifting_Approximation_RectangleScheme
open MultiplierAssoc206.Resolution

namespace LimitsLifting.Approximation

theorem lemma_4_10 :
    ∃ Δ₀ : ℝ, ∀ Δ : ℝ, Δ₀ ≤ Δ → ∀ K : ℝ, 0 < K → ∃ K' : ℝ, 0 < K' ∧ ∃ n₀ : ℕ,
      ∀ n m : ℕ, n₀ ≤ n → (m : ℝ) = (n : ℝ) ^ Δ → ∀ σ : RectScheme n m, IsRectangleScheme n m K σ →
        ∀ F : CNF (Fin n), StandingCNF F → ∀ w : ℝ, 0 < w → w ≤ n →
          ∀ g ∈ liftModel σ w F, RectDense (24 / 25) (rectOf g) →
            ∃ π : List (Clause (Fin n)), IsRefutation F π ∧ (derivWidth π : ℝ) ≤ K' * w := by sorry

end LimitsLifting.Approximation
