-- Prove2me | Theorems.Thm_FriedgutCoalition_lemma_3_5
-- name    : FriedgutCoalition.lemma_3_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:35:33.653434+00:00
-- url     : https://prove2.me/theorems/e7e29a02-f9b4-4f33-beff-11baf5c077ec
-- title:
--   Lemma 3.5 — encoding a monotone $f:[r]^n\to\{0,1\}$ by $p$-biased bits
-- statement:
--   Let $r,n\in\mathbb N$ and let $f:[r]^n\to\{0,1\}$ be monotone. For all $\varepsilon>0$ and $p\in(0,1/2)$ there are $m\in\mathbb N$ and $g:\{0,1\}^m\to\{0,1\}$ such that:
--
--   1. $g$ is monotone;
--   2. $\big|\mathbb E_{y\sim\mu_p}[g(y)]-\mathbb E_{x\sim U_n}[f(x)]\big|\le prn$;
--   3. $\mathbf I^p(g)\le2\cdot\mathbf J^0(f)+4pr\cdot n^2$;
--   4. for every $S\subseteq[m]$ with $\mathbf P^1_S(g,\mu_p)\ge1-\varepsilon$ there is $T\subseteq[n]$ with $|T|\le|S|$ and
--
--   $$\mathbf P^1_T(f)\ge1-\varepsilon-prn.$$
--
--   The lemma converts influence towards $0$ on a large alphabet into $p$-biased influence on bits, so that Theorem 3.4 can be applied.
--
--   Differences from the source:
--   - encoding: {0,1}, [n], [r] = {1,…,r} → Bool (false < true), Fin n, Fin r (the value 1 of [r] is 0 : Fin r, the value r is its top); reason: Lean conventions; the same instances
--   - encoding: r ∈ ℕ (an alphabet [r] = {1,…,r}) → any r : ℕ, including r = 0; reason: at r = 0 and n ≥ 1 the domain [0]ⁿ is empty and the lemma (take g constant) holds trivially; no instance with r ≥ 1 changes
-- source:
--   Chattopadhyay, Gurumukhani, A Resolution of Friedgut's Conjecture on Influential Coalitions, arXiv:2609.16401 (held file sha256 51f298ff…), Lemma 3.5, pp.9–10

import Mathlib
import Definitions.Def_FriedgutCoalition_coalProb
import Definitions.Def_FriedgutCoalition_pInfl

namespace FriedgutCoalition

/-- **Lemma 3.5** (Chattopadhyay–Gurumukhani, arXiv:2609.16401 (held file sha256 51f298ff…), pp.9–10). For `r, n ∈ ℕ` let
`f : [r]ⁿ → {0,1}` be monotone. Then for all `ε > 0` and `p ∈ (0, 1/2)` there are `m ∈ ℕ` and
`g : {0,1}^m → {0,1}` such that
1. `g` is monotone;
2. `|E_{y∼µ_p}[g(y)] − E_{x∼Uₙ}[f(x)]| ≤ prn`;
3. `I^p(g) ≤ 2 · J⁰(f) + 4pr · n²`;
4. for every `S ⊆ [m]` with `P¹_S(g, µ_p) ≥ 1 − ε` there is `T ⊆ [n]` with `|T| ≤ |S|` and
   `P¹_T(f) ≥ 1 − ε − prn`.

**Formalization Note.** `[r]ⁿ` is `Fin n → Fin r` with `unif r`, `{0,1}^m` is `Fin m → Bool` with
`µ_p`. No hypothesis on `r` (the statement holds trivially at `r = 0`). -/
theorem lemma_3_5 (r n : ℕ) (f : (Fin n → Fin r) → Bool) (hf : Monotone f) :
    ∀ ε : ℝ, 0 < ε → ∀ p : ℝ, 0 < p → p < 1 / 2 →
      ∃ (m : ℕ) (g : (Fin m → Bool) → Bool),
        Monotone g ∧
        |outProb (bern p) g true - outProb (unif r) f true| ≤ p * r * n ∧
        totalPInfl p g ≤ 2 * totalToward (unif r) f false + 4 * p * r * (n : ℝ) ^ 2 ∧
        ∀ S : Finset (Fin m), 1 - ε ≤ coalProb (bern p) g S true →
          ∃ T : Finset (Fin n), T.card ≤ S.card ∧
            1 - ε - p * r * n ≤ coalProb (unif r) f T true := by sorry

end FriedgutCoalition
