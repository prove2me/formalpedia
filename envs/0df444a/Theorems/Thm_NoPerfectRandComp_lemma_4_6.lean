-- Prove2me | Theorems.Thm_NoPerfectRandComp_lemma_4_6
-- name    : NoPerfectRandComp.lemma_4_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:45:04.955305+00:00
-- url     : https://prove2.me/theorems/55eb70c4-e2d3-4788-8b14-934651f006f6
-- title:
--   Lemma 4.6 — list direct product, $\Pr[\text{list correct}]\le L\,2^{\lfloor Q/(R_0+1)\rfloor}\beta^c$
-- statement:
--   Let $\mu$ be a distribution on the domain of a partial Boolean function $f$, and suppose every decision tree of depth at most $R_0$ has success at most $\beta$ under $\mu$. Consider a tree that makes at most $Q$ queries to $c$ independent inputs $X_1,\dots,X_c \sim \mu$ and outputs a list of at most $L$ vectors in $\{0,1\}^c$. Then
--   $$
--   \Pr\big[\text{the list contains } (f(X_1),\dots,f(X_c))\big] \ \le\ L\, 2^{\lfloor Q/(R_0+1)\rfloor}\,\beta^c ,
--   $$
--   and the same bound holds for randomized trees.
--
--   It converts the hardness of one core into the hardness of guessing a short list containing the answer vector of all $c$ cores.
--
--   **Formalization Note** The $c$ inputs are the blocks of a tree on $c$ copies of the coordinates; a list is a finite set of answer vectors at each leaf; the product distribution is written as a finite sum with weights $\prod_i \mu(X_i)$. Both the deterministic and the randomized clause are stated.
--
--   Differences from the source:
--   - encoding: lists of at most L vectors → finite sets of at most L answer vectors at every leaf; reason: the event "the list contains all c answers" depends only on the set
-- source:
--   Meiburg, No Perfect Randomized Composition, arXiv:2610.31638 (held version, sha256 5122a74a…), Lemma 4.6, p.15

import Mathlib
import Definitions.Def_QAlgorithms_Defs_Classical
import Definitions.Def_NoPerfectRandComp_PartialFn

namespace NoPerfectRandComp

/-- Lemma 4.6 of Meiburg, *No Perfect Randomized Composition*, arXiv:2610.31638 (held version, sha256 5122a74a…aeae3), p.15 (list direct product): let `μ` be a distribution on the domain of a
partial Boolean function `f`, and suppose every tree of depth at most `R₀` has success at most `β`
under `μ`. A tree making at most `Q` queries to `c` independent inputs from `μ` and outputting a
list of at most `L` vectors in `{0,1}^c` satisfies
`Pr[the list contains all c answers] ≤ L · 2^{⌊Q/(R₀+1)⌋} · β^c`; the same bound holds for
randomized trees.

**Formalization Note** The `c` inputs are the blocks `X i` of a tree on `Fin c × ι`; a list is a
`Finset` of answer vectors at each leaf, of size at most `L` on every input. The product
distribution `μ^c` is written as the finite sum with weights `∏ i μ(X i)`. Both the deterministic
and the randomized clause are stated. -/
theorem lemma_4_6 {ι : Type} [Fintype ι] [DecidableEq ι] (f : PartialFn ι) (μ : PMF (ι → Bool))
    (hμ : ∀ x ∈ μ.support, x ∈ f.dom) (R₀ : ℕ) (β : ℝ)
    (hβ : ∀ T : QAlgorithms.DecisionTree ι Bool Bool, T.MakesAtMost R₀ →
      ∑ x, (if T.eval x = f.val x then (μ x).toReal else 0) ≤ β)
    (c Q L : ℕ) :
    (∀ T : QAlgorithms.DecisionTree (Fin c × ι) Bool (Finset (Fin c → Bool)), T.MakesAtMost Q →
      (∀ X, (T.eval X).card ≤ L) →
      ∑ X : Fin c → ι → Bool, (∏ i, (μ (X i)).toReal) *
          (if (fun i => f.val (X i)) ∈ T.eval (fun p => X p.1 p.2) then 1 else 0)
        ≤ L * 2 ^ (Q / (R₀ + 1)) * β ^ c) ∧
    (∀ A : QAlgorithms.RandDecisionTree (Fin c × ι) Bool (Finset (Fin c → Bool)),
      QAlgorithms.RandMakesAtMost A Q →
      (∀ T ∈ A.support, ∀ X, (T.eval X).card ≤ L) →
      ∑ X : Fin c → ι → Bool, (∏ i, (μ (X i)).toReal) *
          ((A.map (fun T => T.eval (fun p => X p.1 p.2))).toOuterMeasure
            {S | (fun i => f.val (X i)) ∈ S}).toReal
        ≤ L * 2 ^ (Q / (R₀ + 1)) * β ^ c) := by sorry

end NoPerfectRandComp
