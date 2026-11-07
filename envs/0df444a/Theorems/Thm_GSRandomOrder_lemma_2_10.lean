-- Prove2me | Theorems.Thm_GSRandomOrder_lemma_2_10
-- name    : GSRandomOrder.lemma_2_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T17:00:58.653466+00:00
-- url     : https://prove2.me/theorems/afd5bc52-d81e-4dcc-a99a-1572b77b45fb
-- title:
--   Lemma 2.10 — safe region: submodularity on the domain and monotonicity inside a canonical demand
-- statement:
--   Let $v$ be a GS valuation.
--
--   1. If $Q\subseteq R$, $g\notin R$ and $R+g\in\operatorname{dom}v$, then $v(g\mid R)\le v(g\mid Q)$, where $v(g\mid S)=v(S+g)-v(S)$.
--   2. If $X=D_v(T)$ for some $T$, then $2^X\subseteq\operatorname{dom}v$ and $v$ is nondecreasing on $2^X$; in particular $v(Y)\ge0$ for every $Y\subseteq X$.
--
--   Inside a canonical demand a signed GS valuation behaves like a nonnegative monotone one, which is why the algorithm's output keeps its value.
--
--   **Formalization Note** Part 1 is written additively, $v(R+g)+v(Q)\le v(R)+v(Q+g)$ in `WithBot ℝ`; all four sets lie in $\operatorname{dom}v$ under the hypotheses, so this is the marginal inequality.
--
--   Differences from the source:
--   - encoding: GS valuation (Definition 2.1, equivalently the exchange axiom (3) by the cited Theorem 2.3, p.6), values in ℝ ∪ {−∞} → IsGSValuation v: v ∅ = 0 and the exchange axiom (3), v : Finset (Fin n) → WithBot ℝ; reason: the paper defines a GS valuation as one with the two equivalent properties and all its proofs use (3); ⊥ = −∞
--   - encoding: v(g | R) ≤ v(g | Q) → v(R + g) + v(Q) ≤ v(R) + v(Q + g) in WithBot ℝ; reason: all four sets are subsets of R + g ∈ dom v, hence finite (Lemma 2.5), so the two forms are equivalent
-- source:
--   Paes Leme, Pál, Patel, Gross Substitutes Welfare in Random Order, STOC 2027 submission (manuscript sha256 69787f50…), Lemma 2.10, p.8

import Mathlib
import Definitions.Def_GSRandomOrder_IsGSValuation
import Definitions.Def_GSRandomOrder_canonicalDemand

set_option autoImplicit false

namespace GSRandomOrder

/-- **Lemma 2.10 (Safe region)** (Paes Leme, Pál, Patel, *Gross Substitutes Welfare in Random
Order*, STOC 2027 submission, manuscript sha256 69787f50…, §2.3, p.8). Let `v` be a GS valuation.
(a) If `Q ⊆ R`, `g ∉ R` and `R + g ∈ dom v`, then `v(g | R) ≤ v(g | Q)`.
(b) If `X = D_v(T)` for some `T`, then `2^X ⊆ dom v` and `v` is nondecreasing on `2^X`; in
particular `v(Y) ≥ 0` for every `Y ⊆ X`.

**Formalization Note.** In (a) the marginal inequality `v(R + g) − v(R) ≤ v(Q + g) − v(Q)` is
written additively, `v(R + g) + v(Q) ≤ v(R) + v(Q + g)` in `WithBot ℝ`. Under the hypotheses all
four sets lie in `dom v` (they are subsets of `R + g`, and `dom v` is closed under subsets by
Lemma 2.5), so the two forms are equivalent. (b) is stated for every `T`, with its three parts. -/
theorem lemma_2_10 {n : ℕ} (v : Finset (Fin n) → WithBot ℝ) (hv : IsGSValuation v) :
    (∀ (Q R : Finset (Fin n)) (g : Fin n), Q ⊆ R → g ∉ R → v (insert g R) ≠ ⊥ →
      v (insert g R) + v Q ≤ v R + v (insert g Q)) ∧
    ∀ T : Finset (Fin n),
      (∀ Y ⊆ canonicalDemand v T, v Y ≠ ⊥) ∧
      (∀ Y Z : Finset (Fin n), Y ⊆ Z → Z ⊆ canonicalDemand v T → v Y ≤ v Z) ∧
      ∀ Y ⊆ canonicalDemand v T, 0 ≤ v Y := by sorry

end GSRandomOrder
