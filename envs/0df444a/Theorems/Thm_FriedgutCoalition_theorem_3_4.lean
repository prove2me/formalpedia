-- Prove2me | Theorems.Thm_FriedgutCoalition_theorem_3_4
-- name    : FriedgutCoalition.theorem_3_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:35:41.81544+00:00
-- url     : https://prove2.me/theorems/eaa49678-85af-430d-ac81-26750632f0e0
-- title:
--   Theorem 3.4 (Hatami [Hat12, Cor. 2.10], simplified) — small $p$-biased influence gives a small coalition forcing $1$
-- statement:
--   For every $\varepsilon\in(0,1)$ there is a constant $C=C(\varepsilon)\ge1$ such that for all $n\in\mathbb N$, $0<p\le\tfrac12$ and every monotone $f:\{0,1\}^n\to\{0,1\}$ with $\mathbb E_{x\sim\mu_p}[f(x)]\ge\varepsilon$ there is $S\subseteq[n]$ with
--
--   $$|S|\le\exp\big(C\cdot(\mathbf I^p(f))^2\big)\qquad\text{and}\qquad\mathbf P^1_S(f,\mu_p)\ge1-\varepsilon.$$
--
--   Here $\mu_p$ sets each bit to $1$ independently with probability $p$, and $\mathbf I^p(f)$ is the total resampling influence of Definition 2.1. The bound is uniform in $n$ and in $p$.
--
--   The paper cites this as a simplified version of Corollary 2.10 of H. Hatami, *A structure theorem for Boolean functions with small total influences*, Annals of Mathematics 176 (2012). It is the external ingredient of the proof of Lemma 3.3.
--
--   Differences from the source:
--   - encoding: {0,1}, [n], [r] = {1,…,r} → Bool (false < true), Fin n, Fin r (the value 1 of [r] is 0 : Fin r, the value r is its top); reason: Lean conventions; the same instances
-- source:
--   Chattopadhyay, Gurumukhani, A Resolution of Friedgut's Conjecture on Influential Coalitions, arXiv:2609.16401 (held file sha256 51f298ff…), Theorem 3.4, p.9 (citing Hatami, Ann. of Math. 176 (2012), Corollary 2.10)

import Mathlib
import Definitions.Def_FriedgutCoalition_coalProb
import Definitions.Def_FriedgutCoalition_pInfl

namespace FriedgutCoalition

/-- **Theorem 3.4** (simplified version of Corollary 2.10 of Hatami, Annals of Math. 2012, as stated
in Chattopadhyay–Gurumukhani, arXiv:2609.16401 (held file sha256 51f298ff…), p.9). For every `ε ∈ (0,1)` there is `C = C(ε) ≥ 1` such
that for all `n ∈ ℕ`, `0 < p ≤ 1/2` and every monotone `f : {0,1}ⁿ → {0,1}` with
`E_{x∼µ_p}[f(x)] ≥ ε` there is `S ⊆ [n]` with `|S| ≤ exp(C · (I^p(f))²)` and `P¹_S(f, µ_p) ≥ 1 − ε`.

**Formalization Note.** `{0,1}` is `Bool`; `µ_p` is the product of `bern p`; `I^p` is the resampling
influence of Definition 2.1 (`totalPInfl`). `C` comes before `n`, `p` and `f`. -/
theorem theorem_3_4 : ∀ ε : ℝ, 0 < ε → ε < 1 → ∃ C : ℝ, 1 ≤ C ∧
    ∀ (n : ℕ) (p : ℝ), 0 < p → p ≤ 1 / 2 → ∀ f : (Fin n → Bool) → Bool, Monotone f →
      ε ≤ outProb (bern p) f true →
      ∃ S : Finset (Fin n), (S.card : ℝ) ≤ Real.exp (C * (totalPInfl p f) ^ 2) ∧
        1 - ε ≤ coalProb (bern p) f S true := by sorry

end FriedgutCoalition
