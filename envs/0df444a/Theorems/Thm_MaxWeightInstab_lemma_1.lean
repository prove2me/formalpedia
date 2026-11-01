-- Prove2me | Theorems.Thm_MaxWeightInstab_lemma_1
-- name    : MaxWeightInstab.lemma_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:11:54.095022+00:00
-- url     : https://prove2.me/theorems/2c5d8c16-9aae-42b8-83d8-3413dae43e71
-- title:
--   Lemma 1 — the external arrival counts are uniformly close to their mean on every window
-- statement:
--   Let $X_0,X_1,\dots$ be independent and identically distributed $\{0,1\}$-valued random variables with $\mathbb P(X_i=1)=p\in[0,1]$, and let $A(t)=X_0+\dots+X_{t-1}$ count the arrivals of the first $t$ time units. For every $\delta>0$ there exist $\eta>0$ and a constant $C$ such that, for all $T\ge C$,
--
--   $$
--   \mathbb P\Big(\sup_{0\le s\le t\le T}\Big|A(t)-A(s)-p\,(t-s)\Big|\le\delta T\Big)\ \ge\ 1-e^{-\eta T},
--   $$
--
--   where $s,t$ range over the integers. In the network of Figure 1 the external arrival count $A_j$ of each queue $j\in\{\mathcal A_1,\dots,\mathcal A_J,\mathcal B_1,\dots,\mathcal B_J\}$ is such a process with $p=a/J$.
--
--   This large-deviation estimate makes the arrival counts approximately deterministic over long windows; it gives the probability of the event $G_M$ in (16).
--
--   **Formalization Note** The statement is made on any probability space carrying the sequence; $\eta$ and $C$ depend only on $p$ and $\delta$.
--
--   Differences from the source:
--   - generalization: the arrival count A_j of an external queue of Figure 1 (Bernoulli(a/J) per time unit) → any i.i.d. {0,1}-valued sequence with success probability p ∈ [0,1], on any probability space; reason: the external arrival counts are such a sequence with p = a/J ∈ (0,1) under (5), so the statement specializes to the source
--   - reading: sup over 0 ≤ s ≤ t ≤ T → integer times s ≤ t ≤ T; reason: the process is indexed by t ∈ ℤ₊ (p.1, p.5) and (19) sums over t = 0, …, T
-- source:
--   Bramson, D'Auria, Walton, Stability and Instability of the MaxWeight Policy, arXiv:1909.10825v2, Lemma 1, p.6

import Mathlib

namespace MaxWeightInstab

/-- **Lemma 1** (Bramson, D'Auria & Walton, arXiv:1909.10825v2, p.6). For any `δ > 0`, there exist `η > 0` and a constant `C` such
that, for all `T ≥ C`,
`ℙ(sup_{0≤s≤t≤T} |A_j(t) − A_j(s) − (a/J)(t − s)| ≤ δT) ≥ 1 − e^{−ηT}`,
for each external queue `j`, whose arrivals are i.i.d. with at most one arrival per time unit.

**Formalization Note.** Stated for any i.i.d. `{0,1}`-valued sequence `X` with success probability
`p ∈ [0, 1]` (the paper's `p = a/J`), on any probability space; `A(t) = X₀ + ⋯ + X_{t−1}` counts the
arrivals of time units `1, …, t`. `η` and `C` depend on `p` and `δ` only. Times `s, t` are
integers. -/
theorem lemma_1 (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    ∀ δ : ℝ, 0 < δ → ∃ η > 0, ∃ C : ℝ, ∀ T : ℝ, C ≤ T →
      ∀ {Ω : Type*} [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω)
        [MeasureTheory.IsProbabilityMeasure P] (X : ℕ → Ω → Bool),
        (∀ n, Measurable (X n)) → ProbabilityTheory.iIndepFun X P →
        (∀ n, P {ω | X n ω = true} = ENNReal.ofReal p) →
        1 - Real.exp (-η * T) ≤
          (P {ω | ∀ s t : ℕ, s ≤ t → (t : ℝ) ≤ T →
            |(∑ i ∈ Finset.range t, (if X i ω then (1 : ℝ) else 0)) -
              (∑ i ∈ Finset.range s, (if X i ω then (1 : ℝ) else 0)) - p * ((t : ℝ) - s)|
              ≤ δ * T}).toReal := by sorry

end MaxWeightInstab
