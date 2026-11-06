-- Prove2me | Theorems.Thm_NewtonLCP_lemma_8_4
-- name    : NewtonLCP.lemma_8_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:29:43.520104+00:00
-- url     : https://prove2.me/theorems/cc8e2cc9-da1a-48db-9938-a58257020868
-- title:
--   Lemma 8.4 — initialization: the embedded system and its central starting point
-- statement:
--   Let $M\in\mathcal P_\star$, $q\in\mathbb R^n$ and let $\Delta$ be a bit bound for $(M,q)$ as in Lemma 8.3; define $\hat x^0,\hat s^0,\tilde q,\hat\mu^0$ by (52) and the embedded system LCP$(\widehat M,\hat q)$. Then:
--
--   1. for every $\kappa$, $M\in\mathcal P_\star(\kappa)$ if and only if $\widehat M\in\mathcal P_\star(\kappa)$, and $\hat\kappa(M)=\hat\kappa(\widehat M)$;
--   2. $(\hat x^0,\hat s^0)$ is a central path point of LCP$(\widehat M,\hat q)$ with parameter $\hat\mu^0$: $(\hat x^0,\hat s^0)\in\mathcal F_{>0}(\widehat M,\hat q)$ and $\hat x^0_i\hat s^0_i=\hat\mu^0$ for all $i$;
--   3. if $((x^*,\tilde x^*),(s^*,\tilde s^*))$ solves LCP$(\widehat M,\hat q)$ and $\tilde x^*=0_n$, then $(x^*,s^*)$ solves LCP$(M,q)$; if $\tilde x^*\neq0_n$, then LCP$(M,q)$ has no solution.
--
--   The embedded system thus has a known starting point on its central path, and any solution of it decides LCP$(M,q)$.
--
--   Differences from the source:
--   - generalization: M ∈ P⋆ ∩ ℚ^{n×n}, q ∈ ℚⁿ, Δ ≤ 2^{O(L)} as in Lemma 8.3 → real M, q and any integer Δ with the bit-bound property (IsBitBound); reason: the proof uses only the bit-bound property of Δ; rational data with Lemma 8.3's Δ satisfy it
--   - reading: M ∈ P⋆(κ) iff M̂ ∈ P⋆(κ) and κ̂(M) = κ̂(M̂) → (∀ κ, M ∈ P⋆(κ) ↔ M̂ ∈ P⋆(κ)) ∧ κ̂(M) = κ̂(M̂); reason: the proof states both facts; this form implies every parse of the sentence
--   - encoding: (x̂⁰, ŝ⁰) is a central path point with µ̂⁰ → (x̂⁰, ŝ⁰) ∈ F_{>0}(M̂, q̂) and x̂⁰ᵢŝ⁰ᵢ = µ̂⁰ for all i; reason: this is the meaning used in the proof (ŝ⁰ = M̂x̂⁰ + q̂, x̂⁰ŝ⁰ = 8n∆³1₂ₙ)
-- source:
--   Ma–Végh–Vladu, Newton Steps are Faster for Linear Complementarity Problems, STOC 2027 submission (manuscript sha256 a70e5eab…), Lemma 8.4, (52), p.30

import Mathlib
import Definitions.Def_NewtonLCP_Handicap
import Definitions.Def_NewtonLCP_BitBound
import Definitions.Def_NewtonLCP_Embedding

namespace NewtonLCP

/-- **Lemma 8.4** (initialization). Ma–Végh–Vladu, *Newton Steps are Faster for Linear Complementarity Problems*, STOC 2027
submission manuscript (sha256 a70e5eab52f43bef42b49a8833f8d0483556c18b939405dba6bc1e25ea0740f8), Lemma 8.4, (52), p.30.

Let `M ∈ P⋆ ∩ ℚⁿˣⁿ`, `q ∈ ℚⁿ`, `L` the total encoding length of `(M, q)` and `∆ ≤ 2^{O(L)}` as in
Lemma 8.3; define `x̂⁰, ŝ⁰, q̃, µ̂⁰` by (52). Then `M ∈ P⋆(κ)` iff `M̂ ∈ P⋆(κ)`, and
`κ̂(M) = κ̂(M̂)`; `(x̂⁰, ŝ⁰)` is a central path point of LCP(M̂, q̂) with `µ̂⁰`. Let
`(x̂*, ŝ*) = ((x*, x̃*), (s*, s̃*))` be any solution to LCP(M̂, q̂). If `x̃* = 0ₙ`, then `(x*, s*)`
solves LCP(M, q). If `x̃* ≠ 0ₙ`, then LCP(M, q) has no solution.

**Formalization Note.** `M, q` are real and `∆` is any integer with the property of Lemma 8.3
(`IsBitBound`); the paper's rational `M, q` and `∆ ≤ 2^{O(L)}` from Lemma 8.3 are a special case
(the size bound and rationality are not used). "Central path point with `µ̂⁰`" is
`(x̂⁰, ŝ⁰) ∈ F_{>0}(M̂, q̂)` and `x̂⁰ᵢŝ⁰ᵢ = µ̂⁰` for every `i`. The embedded index set is `ι ⊕ ι`. -/
theorem lemma_8_4 {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix ι ι ℝ) (q : ι → ℝ)
    (Δ : ℤ) (hM : IsPStar M) (hΔ : IsBitBound M q Δ) :
    (∀ κ : ℝ, IsPStarK M κ ↔ IsPStarK (embedM M) κ) ∧
    handicap M = handicap (embedM M) ∧
    (embedX0 M q Δ, embedS0 M q Δ) ∈ FeasPos (embedM M) (embedQ M q Δ) ∧
    (∀ i, embedX0 M q Δ i * embedS0 M q Δ i = embedMu0 (Fintype.card ι) Δ) ∧
    ∀ xs xt ss st : ι → ℝ,
      IsLCPSol (embedM M) (embedQ M q Δ) (Sum.elim xs xt) (Sum.elim ss st) →
        (xt = 0 → IsLCPSol M q xs ss) ∧ (xt ≠ 0 → ¬ ∃ x s, IsLCPSol M q x s) := by sorry

end NewtonLCP
