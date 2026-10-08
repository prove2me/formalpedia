-- Prove2me | Theorems.Thm_FoundationsML_SVM_talagrands_lemma_v2
-- name    : FoundationsML.SVM.talagrands_lemma_v2
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-10-06T06:19:13.033491+00:00
-- url     : https://prove2.me/theorems/4d3084e7-4d61-4aed-a9d4-a40f7565cfd5
-- title:
--   Lemma 5.7 — Talagrand's lemma (suprema over exactly $H$)
-- statement:
--   **Statement (Lemma 5.7, p. 93, PDF p. 110).** Let $\Phi_1,\dots,\Phi_m$ be $l$-Lipschitz functions from $\mathbb R$ to $\mathbb R$ and $\sigma_1,\dots,\sigma_m$ be Rademacher random variables. Then, for any hypothesis set $H$ of real-valued functions (mapping into a bounded interval $[a,b]$, as Definition 3.1 requires),
--   $$\frac1m\,\mathbb E_\sigma\Big[\sup_{h\in H}\sum_{i=1}^m \sigma_i(\Phi_i\circ h)(x_i)\Big] \le \frac lm\,\mathbb E_\sigma\Big[\sup_{h\in H}\sum_{i=1}^m \sigma_i h(x_i)\Big] = l\,\hat R_S(H).$$
--
--   **Formalization Note.** The retired version took both suprema as `⨆ h ∈ H, …`, which on $\mathbb R$ clips negative suprema at $0$ (the inner supremum over the empty index $h\notin H$ is `sSup ∅ = 0`), destroying the $\sigma\leftrightarrow-\sigma$ cancellation and making the lemma false (disproved with $H=\{0\}$, $\Phi\equiv1$, $l=0$). Both sides now take `sSup` of the image of exactly $H$ (the right-hand side through the corrected `EmpiricalRademacherComplexity`, module `_v2`). The hypothesis that $H$ maps into some $[a,b]$ is Definition 3.1's standing assumption (p. 30), under which every supremum is a genuine real number; for an unbounded $H$ the book's right-hand side is $+\infty$ while Lean's `sSup` would return the junk value $0$. The Lipschitz hypothesis is the two-sided bound $|\Phi_i(x)-\Phi_i(y)|\le l|x-y|$ with one constant $l\ge0$ for all $i$. Edge cases: $H=\emptyset$ or $m=0$ give $0\le0$.
-- source:
--   Mohri, Rostamizadeh & Talwalkar, Foundations of Machine Learning, 2nd ed., MIT Press 2018, p. 93, Lemma 5.7 (PDF p. 110)

import Mathlib
import Definitions.Def_FoundationsML_SVM_EmpiricalRademacherComplexity_v2

namespace FoundationsML.SVM

/-- Lemma 5.7 (Talagrand's lemma; Mohri, Rostamizadeh & Talwalkar, *Foundations of Machine
Learning*, 2nd ed., MIT Press 2018, p. 93, PDF p. 110). Let `Φ_1, …, Φ_m` be `l`-Lipschitz
functions from `ℝ` to `ℝ` and `σ_1, …, σ_m` be Rademacher random variables. Then, for any
hypothesis set `H` of real-valued functions (bounded, as Definition 3.1 requires),
`(1/m) E_σ[sup_{h∈H} ∑_{i=1}^m σ_i (Φ_i∘h)(x_i)] ≤ (l/m) E_σ[sup_{h∈H} ∑_{i=1}^m σ_i h(x_i)]
= l·R̂_S(H)`.

**Formalization Note.** Replaces `talagrands_lemma`, whose suprema `⨆ h ∈ H, …` on `ℝ` were
clipped at `0` (the inner supremum over the empty index `h ∉ H` is `sSup ∅ = 0`), which broke
the `σ ↔ −σ` cancellation and made the lemma false. Both sides now take the supremum over
exactly `H` (`sSup` of the image of `H`; right-hand side through the corrected
`EmpiricalRademacherComplexity`, module `_v2`). The hypothesis `hHb` is Definition 3.1's
standing assumption that the family maps into a bounded interval `[a,b]`, under which every
supremum is a genuine real number (for an unbounded `H` the book's right-hand side is `+∞`
and Lean's `sSup` would return the junk value `0`). The Lipschitz hypothesis is the two-sided
bound `|Φ_i x − Φ_i y| ≤ l |x − y|` with one constant `l ≥ 0` for every `i`. -/
theorem talagrands_lemma_v2 {X : Type*} {m : ℕ} (H : Set (X → ℝ))
    (hHb : ∃ a b : ℝ, ∀ h ∈ H, ∀ x, h x ∈ Set.Icc a b) (S : Fin m → X)
    (Φ : Fin m → ℝ → ℝ) (l : ℝ) (hl : 0 ≤ l)
    (hLip : ∀ i : Fin m, ∀ x y : ℝ, |Φ i x - Φ i y| ≤ l * |x - y|) :
    (1 / (2 : ℝ) ^ m) * ∑ σ : Fin m → Bool,
      sSup ((fun h : X → ℝ =>
        (1 / (m : ℝ)) * ∑ i : Fin m, (if σ i then (1 : ℝ) else -1) * Φ i (h (S i))) '' H)
      ≤ l * EmpiricalRademacherComplexity H S := by sorry

end FoundationsML.SVM
