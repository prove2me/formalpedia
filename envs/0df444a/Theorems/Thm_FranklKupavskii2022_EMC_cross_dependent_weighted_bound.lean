-- Prove2me | Theorems.Thm_FranklKupavskii2022_EMC_cross_dependent_weighted_bound
-- name    : FranklKupavskii2022.EMC.cross_dependent_weighted_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T13:21:38.380748+00:00
-- url     : https://prove2.me/theorems/eac64363-904c-42ed-9c3f-565a886a3520
-- title:
--   Lemma 15: $|\mathcal F_1|+\dots+|\mathcal F_s|+q|\mathcal F_{s+1}|\le s\binom{|Y|}{l}$
-- statement:
--   For every $\epsilon>0$ there is $s_0\in\mathbb N$ such that the following holds for every $s\ge s_0$. Let $Y$ be a finite set and let $\mathcal F_1,\dots,\mathcal F_{s+1}\subseteq\binom Yl$ be cross-dependent and nested, with $|Y|\ge tl$ for some $t\in\mathbb N$. Suppose that for some reals $x,q$ with $x\le s+1$, $0<q\le s+1$ and some $\alpha\in[0,1]$,
--
--   $$
--   |\mathcal F_{s+1}|=\alpha\binom{|Y|}{l},\qquad (\alpha+\epsilon)t\le\frac{sx}{q},\qquad t\ge s+x+1 .
--   $$
--
--   Then
--
--   $$
--   |\mathcal F_1|+|\mathcal F_2|+\dots+|\mathcal F_s|+q|\mathcal F_{s+1}|\le s\binom{|Y|}{l}. \tag{26}
--   $$
--
--   This is the key lemma of the paper: a weighted version of the Erdős matching bound for cross-dependent families, proved by averaging Lemma 18 over a random matching with the concentration of Theorem 12 and Proposition 13. The threshold $s_0$ depends only on $\epsilon$.
--
--   **Formalization Note** The paper states only $x,q\le s+1$; the statement keeps that range and adds only $q>0$, which the division $sx/q$ presupposes.
-- source:
--   Frankl–Kupavskii, The Erdős Matching Conjecture and concentration inequalities, arXiv:1806.08855v3, Lemma 15, p. 9

import Mathlib
import Definitions.Def_FranklKupavskii2022_EMC_CrossDependent
import Definitions.Def_FranklKupavskii2022_EMC_Nested

namespace FranklKupavskii2022.EMC

/-- Lemma 15 (Frankl–Kupavskii, arXiv:1806.08855v3, p. 9): for any `ǫ > 0` there exists `s_0 ∈ ℕ`
such that the following holds for any `s ≥ s_0`. Let `F_1, …, F_{s+1} ⊂ \binom{Y}{l}` be
cross-dependent and nested, and suppose that `|Y| ≥ tl` for some `t ∈ ℕ`. If for some `x, q` with
`x, q ≤ s + 1` and `α ∈ [0, 1]` we have `|F_{s+1}| = α\binom{|Y|}{l}`, `(α + ǫ)t ≤ sx/q`, and
`t ≥ s + x + 1`, then `|F_1| + … + |F_s| + q|F_{s+1}| ≤ s\binom{|Y|}{l}` (26).

**Formalization Note.** `s_0` depends on `ǫ` only (it is chosen before `Y, l, t, x, q, α` and the
families). `x, q, α` are real. The paper bounds `x` and `q` only from above; the statement is
kept literal, with the single addition `0 < q`, which the paper's division `sx/q` presupposes
(in Lean `sx/0 = 0`). The paper's proof applies Lemma 18, which assumes `1 ≤ x, q`; the
remaining range adds nothing false: for `0 < x < 1` the integer `t ≥ s + x + 1` gives
`t ≥ s + 2`, so the case `x = 1` applies; for `x ≤ 0` the hypotheses are unsatisfiable when
`s ≥ 1`; and for `0 < q ≤ 1` the bound follows from the cross-dependent averaging bound
`|F_1| + … + |F_{s+1}| ≤ s\binom{|Y|}{l}` (valid since `|Y| ≥ (s + 1)l`).
The finite ground set `Y` is a `Finset ℕ`; the families are `Fam 1, …, Fam (s + 1)`. -/
theorem cross_dependent_weighted_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ s₀ : ℕ, ∀ s : ℕ, s₀ ≤ s → ∀ (Y : Finset ℕ) (l t : ℕ) (Fam : ℕ → Finset (Finset ℕ))
      (x q α : ℝ),
      (∀ i ∈ Finset.Icc 1 (s + 1), Fam i ⊆ Y.powersetCard l) →
      CrossDependent s Fam → Nested s Fam → t * l ≤ Y.card →
      x ≤ s + 1 → 0 < q → q ≤ s + 1 → 0 ≤ α → α ≤ 1 →
      ((Fam (s + 1)).card : ℝ) = α * (Y.card.choose l : ℝ) →
      (α + ε) * t ≤ s * x / q → (s : ℝ) + x + 1 ≤ t →
      ∑ i ∈ Finset.Icc 1 s, ((Fam i).card : ℝ) + q * (Fam (s + 1)).card ≤
        s * (Y.card.choose l : ℝ) := by sorry

end FranklKupavskii2022.EMC
