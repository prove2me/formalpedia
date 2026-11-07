-- Prove2me | Theorems.Thm_KMeansTaper_theorem_F_1
-- name    : KMeansTaper.theorem_F_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T17:06:39.38122+00:00
-- url     : https://prove2.me/theorems/605be79f-f326-4c03-9c7e-d5b69bf062dc
-- title:
--   Theorem F.1 — reduction, $p=2$
-- statement:
--   There is an absolute constant $C$ such that the following holds. Let $\alpha\ge169/49$, $c\in\mathbb N$ and $0<\varepsilon\le2\alpha$ be rationals and $e=C(\lceil\alpha c/\varepsilon\rceil+1)$. There are a list of queries and a post-processing step such that, for every instance $I$ with $n=|J|+|F|$:
--
--   1. the queries are at most $n^{e}$ restricted facility sets $F'\subseteq F$ with $|F'|\ge k$;
--   2. the queries and the post-processing are computed by deterministic algorithms, a Turing machine (`Turing.TM2ComputableInPolyTime`, every tape alphabet finite) running in time polynomial in the input length, of degree at most $e$;
--   3. whenever the answers $T$ to the queries $F'$ satisfy $T\subseteq F'$, $T\neq\emptyset$, $|T|\le k+c$ and $\mathrm{cost}_2(T)\le\alpha\,\mathrm{opt}_{I'}$, the post-processing returns a nonempty $S\subseteq F$ with $|S|\le k$ and $\mathrm{cost}_2(S)\le(\alpha+\varepsilon)\mathrm{OPT}_k$.
--
--   So an algorithm $A$ with $c$ extra facilities and ratio $\alpha$ on restricted instances gives a true $(\alpha+\varepsilon)$-approximation with $n^{O(\alpha c/\varepsilon)}$ calls to $A$ and $n^{O(\alpha c/\varepsilon)}$ further time.
--
--   **Formalization Note** The reduction is non-adaptive, as in the paper's proof (one call of $A$ on each instance of Lemma F.2). Queries are output as concatenated indicator lists.
--
--   Differences from the source:
--   - reading: n^{O(αc/ε)} calls to A and n^{O(αc/ε)} further time → at most n^{C(⌈αc/ε⌉+1)} queries, and query and post-processing machines whose time polynomials in the input length have degree at most C(⌈αc/ε⌉+1), with one absolute C; reason: the O hides an absolute constant; the +1 covers c = 0, where the algorithm still reads its input; the paper does not fix a time model
--   - reading: a deterministic algorithm using calls to A → a non-adaptive oracle algorithm: a query list computed from I and a post-processing of I and the answers; reason: the paper's algorithm queries A once on each restricted instance of Lemma F.2, independently of the answers
--   - generalization: A is a deterministic algorithm with the guarantee on every restricted instance with |F′| ≥ k → any list of answers with the guarantee on the queried instances; reason: the paper's A supplies such answers
--   - encoding: returns S ⊆ F, |S| ≤ k, cost(S) ≤ (α + ε) opt_I → CorrectRatio (α + ε): indicator list of a nonempty S ⊆ F; reason: the empty set has infinite cost in the paper
--   - encoding: A returns T with cost(T) ≤ α opt_{I'} (finite, so T ≠ ∅) → each answer T is nonempty with cost2 I T ≤ α optimumOn I F'; reason: cost2 I ∅ = 0 is a junk value; the paper's cost(∅) = ∞
-- source:
--   Zhu, A tight approximation for metric k-means via squared tapered rounding, STOC 2027 submission (manuscript sha256 8b6610229e43dc2441325b120437136afe762dbd6e873f73919fcb6b043fc5a3), Theorem F.1, p.43 (PDF p.46); proof pp.44–45 (PDF pp.47–48)

import Mathlib
import Definitions.Def_MetricKMedian
import Definitions.Def_KMeansTaper_cost2
import Definitions.Def_KMeansTaper_CorrectRatio
import Definitions.Def_KMeansTaper_encodePieces

namespace KMeansTaper

open OAI.MetricKMedian (Instance encodeInstance)

/-- **Theorem F.1 (reduction, p = 2)**, p.43 (PDF p.46).

Zhu, *A tight approximation for metric k-means via squared tapered rounding*, STOC 2027
submission (manuscript sha256 8b6610229e43dc2441325b120437136afe762dbd6e873f73919fcb6b043fc5a3).

Let `α ≥ 169/49`, `c ∈ ℕ` and `0 < ε ≤ 2α` be fixed rationals. Suppose a deterministic
algorithm `A`, given any restricted instance `I'` with `|F'| ≥ k`, returns `T ⊆ F'` with
`|T| ≤ k + c` and `cost(T) ≤ α opt_{I'}`. Then there is a deterministic algorithm that returns
`S ⊆ F`, `|S| ≤ k`, `cost(S) ≤ (α + ε) opt_I`, using `n^{O(αc/ε)}` calls to `A` and
`n^{O(αc/ε)}` further time, where `n = |J| + |F|`.

**Formalization Note.** The reduction is non-adaptive (the proof queries `A` once on each
restricted instance of Lemma F.2): `queries I` lists the restricted facility sets, `post`
receives `I` and the answers. `n^{O(αc/ε)}` is read with one absolute constant `C`: at most
`n^{C(⌈αc/ε⌉+1)}` queries, and both `queries` (as the concatenated indicator bit-lists) and
`post` are `Turing.TM2ComputableInPolyTime` machines with finite alphabets whose time polynomial
in the input length has degree at most `C(⌈αc/ε⌉+1)`. The hypothesis on `A` is required only on
the queried instances, through any list of answers; each answer is nonempty (the paper's `A`
returns `T` with `cost(T) ≤ α opt_{I'} < ∞`, and `cost2 I ∅ = 0` is a junk value). -/
theorem theorem_F_1 :
    ∃ C : ℕ, ∀ (α : ℚ) (c : ℕ) (ε : ℚ), 169 / 49 ≤ α → 0 < ε → ε ≤ 2 * α →
      ∃ (queries : (I : Instance) → List (Finset (Fin I.n)))
        (post : (Σ I : Instance, List (Finset (Fin I.n))) → List Bool),
        (∀ I : Instance, (queries I).length
            ≤ (I.clients.card + I.facilities.card) ^ (C * (⌈α * c / ε⌉₊ + 1))) ∧
        (∀ I : Instance, ∀ F' ∈ queries I, F' ⊆ I.facilities ∧ I.k ≤ F'.card) ∧
        (∃ M : Turing.TM2ComputableInPolyTime encodeInstance id
            (fun I => encodeSetList I (queries I)),
          (∀ k : M.tm.K, Finite (M.tm.Γ k)) ∧ M.time.natDegree ≤ C * (⌈α * c / ε⌉₊ + 1)) ∧
        (∃ M : Turing.TM2ComputableInPolyTime encodeAnswers id post,
          (∀ k : M.tm.K, Finite (M.tm.Γ k)) ∧ M.time.natDegree ≤ C * (⌈α * c / ε⌉₊ + 1)) ∧
        ∀ (I : Instance) (answers : List (Finset (Fin I.n))),
          List.Forall₂ (fun T F' => T ⊆ F' ∧ T.Nonempty ∧ T.card ≤ I.k + c ∧
              cost2 I T ≤ α * optimumOn I F') answers (queries I) →
            CorrectRatio (α + ε) I (post ⟨I, answers⟩) := by sorry

end KMeansTaper
