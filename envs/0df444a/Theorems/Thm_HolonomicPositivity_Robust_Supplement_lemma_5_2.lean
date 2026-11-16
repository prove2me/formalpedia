-- Prove2me | Theorems.Thm_HolonomicPositivity_Robust_Supplement_lemma_5_2
-- name    : HolonomicPositivity.Robust.Supplement.lemma_5_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T17:56:50.019449+00:00
-- url     : https://prove2.me/theorems/9e988222-2d23-48c9-bbdf-ba8fe9b268cf
-- title:
--   Lemma 5.2 — computable certificate and unboundedness equivalence
-- statement:
--   There is one partial recursive algorithm taking finite real-algebraic descriptions of $P,Q$ satisfying the coefficient condition of Theorem 3.6 and $P\ne0$. It terminates on every such description and returns real-algebraic descriptions of rational functions $S,L$ and a natural index $N$. These have no poles at natural indices from $N$ onward; $S(k)\ne0$ there if $S\ne0$, and $L(k)\ne0$ there if $S=0$.
--
--   For every real solution of the normalized recurrence, its certificate $C_f(n)$ from (8) satisfies
--   $$n\ge N\ \land\ C_f(n)\quad\Longrightarrow\quad C_f(n+1).$$
--   For every solution positive at all indices $n\ge N$,
--   $$\bigl(\exists n\ge N,\ C_f(n)\bigr)\quad\Longleftrightarrow\quad\widetilde f_{S,L}\text{ is unbounded on }n\ge N.$$
--   The normalized sequence is exactly (9), with empty products equal to one, and unboundedness means absence of a uniform real bound on its absolute values.
--
--   This algorithm supplies the invariant certificate and growth characterization needed for Theorem 3.6. Its guarantees hold for every valid input description, including noncanonical ones.
--
--   Differences from the source:
--   - encoding: an algorithm on real-algebraic rational functions returning S,L,N → Partrec on finite polynomial and isolating-interval descriptions, with every description quantified; reason: standard primitive codings implement the finite inputs and outputs without changing the algebraic domain
--   - encoding: the normalized tail (9), unbounded, with well-defined evaluations → Ico products, absence of an absolute bound for n≥N, and SafeFrom on the computed output; reason: empty products are one; no-pole and nonzero-factor guarantees follow from the source construction on pp.9-11
--   - encoding: real solutions defined from N onward → global IsSolution P Q f, with positivity required only from N onward; reason: Q(n)≠0 lets every tail solution extend uniquely backwards, so no tail instance is lost
-- source:
--   Fugen Hagihara, Positivity Proofs for Third-Order Holonomic Sequences via Differences Scaled by Rational Functions, STOC 2027 submission #328 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/328.pdf, SHA-256 b828a1da95302dcc4eef96a5cd5df68531d46030b0db425e11667ab782afead2; Lemma 5.2, PDF p.9–10 (printed XX:9–XX:10); global assumptions PDF pp.1-2, real eventual comparisons PDF pp.4-5; proof §5.1.1-5.1.3 or §5.2 as applicable.

import Mathlib
import Definitions.Def_HolonomicPositivity_Robust_Supplement_Conditions
import Definitions.Def_HolonomicPositivity_Robust_Supplement_Inputs

namespace HolonomicPositivity.Robust.Supplement

/-- Lemma 5.2, Fugen Hagihara, STOC 2027 submission #328 (October 2026), PDF pp.9-10,
printed XX:9-10. One partial recursive algorithm works on every valid finite description.
Its output is well-defined and has both invariance and the full unboundedness equivalence. -/
theorem lemma_5_2 :
    ∃ alg : CoeffInput →. CertOutput, Partrec alg ∧
      ∀ (P Q : RatFunc ℝ), CoeffCond P Q → P ≠ 0 →
        ∀ d : CoeffInput, CoeffDenotes d P Q →
          (alg d).Dom ∧
          ∀ o ∈ alg d, ∃ S L : RatFunc ℝ,
            CoeffDenotes o.1 S L ∧ SafeFrom S L o.2 ∧
            (∀ f : ℕ → ℝ, IsSolution P Q f →
              ∀ n ≥ o.2, Certificate S L f n → Certificate S L f (n + 1)) ∧
            (∀ f : ℕ → ℝ, IsSolution P Q f → (∀ n ≥ o.2, 0 < f n) →
              ((∃ n ≥ o.2, Certificate S L f n) ↔
                UnboundedFrom o.2 (normalized S L o.2 f))) := by sorry

end HolonomicPositivity.Robust.Supplement
