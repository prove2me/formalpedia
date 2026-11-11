-- Prove2me | Theorems.Thm_LimitsLifting_Approximation_lemma_4_11
-- name    : LimitsLifting.Approximation.lemma_4_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:39:10.661013+00:00
-- url     : https://prove2.me/theorems/82c4d2d1-1609-4ab0-ac93-bce67f3a949d
-- title:
--   Lemma 4.11 — approximators err (corrected: excludes empty clauses)
-- statement:
--   Let $F$ be an unsatisfiable CNF over $[n]$ in which every variable occurs, no clause is tautological and (correction) no clause is empty. Let $m=n^\Delta$, let $f=f_{\mathcal R_{F,\mathrm{Ind}_m}}$, and let $\mathcal M_w$ be the approximation model built from a Rectangle Scheme with constant $K$.
--
--   For every sufficiently large real $\Delta$ and every $K>0$ there are $a>0$ and $n_0$ such that for all $n\ge n_0$, every such scheme and every such $F$, some parameter $w$ with $0<w\le n$ and $w\ge a\,w_{\mathrm{Res}}(F)$ satisfies, for every $g\in\mathcal M_w$,
--   $$\Pr_{x\in f^{-1}(b),\ b\in\{0,1\}}[g(x)=f(x)]\le 0.99,$$
--   under the balanced law; in particular $\varepsilon_{\mathcal M_w}(f)\ge 0.01$.
--
--   The lemma says that no function of the model, however large its circuit, agrees with $f$ on more than $99\%$ of the balanced law; it supplies the numerator of $\mu(f,\mathcal M_w)$ in the main theorem.
--
--   **Formalization Note** $\Omega(w_{\mathrm{Res}}(F))$ is $a\,w_{\mathrm{Res}}(F)$ with $a$ fixed before $n$, the scheme and $F$; $\varepsilon=\Omega(1)$ is stated with the explicit constant $0.01=1-0.99$. Without the correction the statement is false: for $F_n=\{\varnothing\}\cup\{\{x_i\}:i\in[n]\}$ (unsatisfiable, every variable occurs, no tautology) the coordinate $(\varnothing,())$ is an input of $\mathcal M_w$ equal to $f$ on its whole domain, so it agrees with $f$ with probability $1$.
--
--   Differences from the source:
--   - correction: F any unsatisfiable CNF satisfying the §4.3 assumptions → F additionally has no empty clause; reason: for F_n = {∅} ∪ {{x_i}} the input coordinate of the empty clause equals f on Z_{m,n}, so the success probability is 1 > 0.99.
--   - generalization: the Rectangle Scheme of [GGKS20] → every deterministic scheme with the properties of Lemma 4.7 (constant K); reason: the source states only these properties of the scheme ("We merely state the properties of the algorithm that we will use", printed p.20) and its proofs use only them; in M_w the scheme is applied only at gates, never to the input leaves (Definition 4.9); the [GGKS20] scheme has these properties (Lemma 4.7), so the statement specializes to the source's.
--   - encoding: m = n^Δ for a large enough constant Δ → real Δ ≥ Δ₀, with integer m and (m : ℝ) = (n : ℝ)^Δ; reason: preserves all admissible real exponents; block length is an integer, with no rounding or restriction to integer exponents.
--   - encoding: [m], [n] → Fin m, Fin n; reason: index shift, same instances.
-- source:
--   Gaia Carenini, Bruno Cavalar, Stefan Grosser, Jan Pich, Limits of Lifting, STOC 2027 submission #309 (October 2026), Lemma 4.11, printed p. 22 (PDF p. 23); standing assumptions §4.3, printed p. 21 (PDF p. 22)

import Mathlib
import Definitions.Def_MultiplierAssoc206_Resolution_CNF
import Definitions.Def_LimitsLifting_Approximation_ApproxModel
import Definitions.Def_LimitsLifting_Approximation_CanonicalCover
import Definitions.Def_LimitsLifting_Approximation_RectangleScheme
open MultiplierAssoc206.Resolution

namespace LimitsLifting.Approximation

theorem lemma_4_11 :
    ∃ Δ₀ : ℝ, ∀ Δ : ℝ, Δ₀ ≤ Δ → ∀ K : ℝ, 0 < K → ∃ a : ℝ, 0 < a ∧ ∃ n₀ : ℕ,
      ∀ n m : ℕ, n₀ ≤ n → (m : ℝ) = (n : ℝ) ^ Δ → ∀ σ : RectScheme n m, IsRectangleScheme n m K σ →
        ∀ F : CNF (Fin n), StandingCNF F → ∅ ∉ F →
          ∃ w : ℝ, 0 < w ∧ w ≤ n ∧ a * (wRes F : ℝ) ≤ w ∧
            (∀ g ∈ liftModel σ w F,
              balancedProb (liftedFn m F) (fun z => g z = liftedFn m F z) ≤
                99 / 100) ∧
            1 / 100 ≤ liftEps σ w F := by sorry

end LimitsLifting.Approximation
