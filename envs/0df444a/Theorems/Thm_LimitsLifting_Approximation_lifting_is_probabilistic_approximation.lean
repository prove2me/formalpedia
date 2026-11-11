-- Prove2me | Theorems.Thm_LimitsLifting_Approximation_lifting_is_probabilistic_approximation
-- name    : LimitsLifting.Approximation.lifting_is_probabilistic_approximation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:39:05.657198+00:00
-- url     : https://prove2.me/theorems/03123270-a828-41af-bb9b-52bd4ba38116
-- title:
--   Theorem 4.12 — DAG-like lifting is probabilistic approximation (corrected: excludes empty clauses)
-- statement:
--   Let $F$ be an unsatisfiable CNF over $[n]$ in which every variable occurs, no clause contains a literal and its negation, and (correction) no clause is empty. Let $m=n^\Delta$, let $f=f_{\mathcal R_{F,\mathrm{Ind}_m}}$ be the partial monotone function of Razborov's reduction on the canonical rectangle cover, and let $\mathcal M_w$ be the approximation model built from a Rectangle Scheme with the properties of Lemma 4.7, with constant $K$.
--
--   For every sufficiently large real $\Delta$ and every $K>0$ there are constants $a,c>0$ and $n_0$ such that for all $n\ge n_0$, every such scheme and every such $F$:
--   1. there is a parameter $w$ with $0<w\le n$ and $w\ge a\,w_{\mathrm{Res}}(F)$ such that
--   $$\mu(f,\mathcal M_w)\ge\frac{1}{200}\,n^{w};$$
--   2. the monotone circuit complexity of $f$ satisfies
--   $$\mathrm{Size}^+(f)\ge n^{c\,w_{\mathrm{Res}}(F)}.$$
--
--   The theorem recovers the dag-like lifting lower bound of Garg, Göös, Kamath and Sokolov as an instance of Razborov's approximation method; by Razborov's limitation of the method, such arguments cannot give more than linear lower bounds for non-monotone circuits.
--
--   **Formalization Note** $\Omega(w_{\mathrm{Res}}(F))$ and $n^{\Omega(w_{\mathrm{Res}}(F))}$ are $a\,w_{\mathrm{Res}}(F)$ and $n^{c\,w_{\mathrm{Res}}(F)}$ with $a,c$ fixed before $n$, the scheme and $F$. The prefactor $\frac1{200}$ of $\Omega(n^w)$ is the one supplied by the proof: $\varepsilon\ge 1/100$ (Lemma 4.11) and $\delta\le 2n^{-w}$. $\mu=\varepsilon/\delta$ is a real quotient, so the first conclusion also asserts $\delta>0$. Without the correction the statement is false: for $F_n=\{\varnothing\}\cup\{\{x_i\}:i\in[n]\}$ the input coordinate of the empty clause equals $f$, so $\varepsilon=0$ and $\mu=0$ for every $w$.
--
--   Differences from the source:
--   - correction: F any unsatisfiable CNF satisfying the §4.3 assumptions → F additionally has no empty clause; reason: for F_n = {∅} ∪ {{x_i}} the input coordinate of the empty clause is a member of M_w equal to f, so ε = 0 and µ(f, M_w) = 0 < Ω(n^w).
--   - generalization: the Rectangle Scheme of [GGKS20] → every deterministic scheme with the properties of Lemma 4.7 (constant K); reason: the source states only these properties of the scheme ("We merely state the properties of the algorithm that we will use", printed p.20) and its proofs use only them; in M_w the scheme is applied only at gates, never to the input leaves (Definition 4.9); the [GGKS20] scheme has these properties (Lemma 4.7), so the statement specializes to the source's.
--   - encoding: m = n^Δ for a large enough constant Δ → real Δ ≥ Δ₀, with integer m and (m : ℝ) = (n : ℝ)^Δ; reason: preserves all admissible real exponents; block length is an integer, with no rounding or restriction to integer exponents.
--   - encoding: [m], [n] → Fin m, Fin n; reason: index shift, same instances.
-- source:
--   Gaia Carenini, Bruno Cavalar, Stefan Grosser, Jan Pich, Limits of Lifting, STOC 2027 submission #309 (October 2026), Theorem 4.12, printed p. 22 (PDF p. 23); standing assumptions §4.3, printed p. 21 (PDF p. 22)

import Mathlib
import Definitions.Def_MultiplierAssoc206_Resolution_CNF
import Definitions.Def_LimitsLifting_Approximation_ApproxModel
import Definitions.Def_LimitsLifting_Approximation_CanonicalCover
import Definitions.Def_LimitsLifting_Approximation_RectangleScheme
open MultiplierAssoc206.Resolution

namespace LimitsLifting.Approximation

theorem lifting_is_probabilistic_approximation :
    ∃ Δ₀ : ℝ, ∀ Δ : ℝ, Δ₀ ≤ Δ → ∀ K : ℝ, 0 < K →
      ∃ a c : ℝ, 0 < a ∧ 0 < c ∧ ∃ n₀ : ℕ, ∀ n m : ℕ, n₀ ≤ n → (m : ℝ) = (n : ℝ) ^ Δ →
        ∀ σ : RectScheme n m, IsRectangleScheme n m K σ →
          ∀ F : CNF (Fin n), StandingCNF F → ∅ ∉ F →
            (∃ w : ℝ, 0 < w ∧ w ≤ n ∧ a * (wRes F : ℝ) ≤ w ∧
                (1 / 200 : ℝ) * (n : ℝ) ^ w ≤ liftMu σ w F) ∧
              (n : ℝ) ^ (c * (wRes F : ℝ)) ≤ (monotoneSize (liftedFn m F) : ℝ) := by sorry

end LimitsLifting.Approximation
