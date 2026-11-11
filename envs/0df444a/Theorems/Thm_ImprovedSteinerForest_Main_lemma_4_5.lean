-- Prove2me | Theorems.Thm_ImprovedSteinerForest_Main_lemma_4_5
-- name    : ImprovedSteinerForest.Main.lemma_4_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T01:26:43.87546+00:00
-- url     : https://prove2.me/theorems/4b0c37ae-041a-4062-9817-26d63ed82f3d
-- title:
--   Lemma 4.5 — truncated deletion time: β·E min(x, j) ≤ φ_k(b_j), and Pr(x > j) ≤ 1 − b_j for one witness
-- statement:
--   There are initially $k$ witnesses. Rounds are numbered $1,2,\dots$; the past after $r$ rounds is the $\sigma$-algebra $\mathcal F_r$ of a filtration, and the event that witness $i$ is marked within the first $r$ rounds is $\mathcal F_r$-measurable, empty for $r=0$ and increasing in $r$. Conditional on $\mathcal F_r$, each witness not yet marked is marked in round $r+1$ with probability at least $\beta$, where $0<\beta\le 1$; marks within a round may be dependent. Let $x$ be the first round by which all witnesses are marked ($x=0$ when $k=0$, $x=\infty$ if this never happens). For every integer $j\ge0$ put
--   $$b_j=1-(1-\beta)^j,\qquad \varphi_k(b)=\sum_{h=1}^{k}\frac{b^h}{h},\ \ \varphi_0(b)=0.$$
--   Then
--   $$\beta\,\mathbb E\min(x,j)\le\varphi_k(b_j),\tag{4.6}$$
--   and, for one witness ($k=1$), $\Pr(x>j)\le 1-b_j$.
--
--   The lemma bounds how many rounds of the rounding routine a reference edge with $k$ witnesses can be charged before it is deleted; it is used only through the marking probability, with no independence.
--
--   **Formalization Note.** The probability space is arbitrary, with a probability measure `P` and a filtration `ℱ` indexed by rounds. The conditional marking probability is the conditional expectation of the indicator of "marked within $r+1$ rounds" given `ℱ r`, required to be at least `β` almost surely on "not marked within $r$ rounds". $x$ takes values in `ℕ∞`, and $\min(x,j)$ is integrated as a real number.
--
--   Differences from the source:
--   - encoding: "conditional on the entire past" → a filtration `ℱ`, marked events adapted to it, and `condExp (ℱ r) P (indicator) ≥ β` a.e. on the unmarked event; reason: the standard rendering of a conditional probability bound given the past.
--   - encoding: x = first round when all are marked → `x : Ω → ℕ∞`, the infimum of the rounds by which all are marked (`⊤` if none); reason: the round may not exist; `min(x, j)` is finite.
-- source:
--   Cheshm Jahan, Keshavarz Hedayati, Safari, Shahrezaei, Improved Steiner Forest Approximation via Cut Spaces, STOC 2027 submission (manuscript sha256 b2bf022d…0444), p. 24, Lemma 4.5

import Mathlib

namespace ImprovedSteinerForest.Main

/-- Lemma 4.5 (Truncated deletion time, p. 24): `k` witnesses; conditional on the entire past
(the filtration `ℱ`), each remaining witness is marked in the next round with probability at least
`β ∈ (0, 1]`; `x` is the first round when all are marked (`x = 0` when `k = 0`, `x = ⊤` if never).
Then `β E min(x, j) ≤ φ_k(b_j)` with `b_j = 1 − (1 − β)^j`, `φ_k(b) = Σ_{h=1}^k b^h/h`, and for one
witness `Pr(x > j) ≤ 1 − b_j`. -/
theorem lemma_4_5 {Ω : Type*} [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure P]
    (ℱ : MeasureTheory.Filtration ℕ (inferInstance : MeasurableSpace Ω))
    (k : ℕ) (β : ℝ) (hβ : 0 < β) (hβ1 : β ≤ 1)
    (marked : Fin k → ℕ → Set Ω)
    (h0 : ∀ i, marked i 0 = ∅)
    (hmono : ∀ i r, marked i r ⊆ marked i (r + 1))
    (hadapt : ∀ i r, @MeasurableSet Ω (ℱ r) (marked i r))
    (hmark : ∀ i r, ∀ᵐ ω ∂P, ω ∉ marked i r →
      β ≤ MeasureTheory.condExp (ℱ r) P ((marked i (r + 1)).indicator (fun _ => (1 : ℝ))) ω)
    (x : Ω → ℕ∞) (hx : ∀ ω, x ω = ⨅ (r : ℕ) (_ : ∀ i, ω ∈ marked i r), (r : ℕ∞))
    (j : ℕ) :
    β * ∫ ω, ((min (x ω) (j : ℕ∞)).toNat : ℝ) ∂P ≤
        ∑ h ∈ Finset.Icc 1 k, (1 - (1 - β) ^ j) ^ h / (h : ℝ) ∧
      (k = 1 → (P {ω | (j : ℕ∞) < x ω}).toReal ≤ 1 - (1 - (1 - β) ^ j)) := by sorry

end ImprovedSteinerForest.Main
