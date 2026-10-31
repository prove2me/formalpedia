-- Prove2me | Theorems.Thm_LinearZeroSumMG_lemma_11
-- name    : LinearZeroSumMG.lemma_11
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:52:07.458801+00:00
-- url     : https://prove2.me/theorems/46915912-e829-4624-94bb-ec1e348631bc
-- title:
--   Lemma 11, p.29 — $\mathcal N_\varepsilon\le2(1+8H\sqrt{dk}/\varepsilon)^d(1+8\max\{\beta^2,\beta^4\}\sqrt d/\varepsilon^2)^{d^2}$ (corrected: $\max\{\beta^2,\beta^4\}$ for the printed $\beta^2$)
-- statement:
--   **Lemma 11 (Covering), corrected.** Let $\phi:\mathcal S\times\mathcal A\times\mathcal A\to\mathbb R^d$ satisfy $\|\phi(x,a,b)\|\le1$, let $H,k\in\mathbb N$, $\beta>0$ and $\varepsilon>0$, and let $\mathcal Q$ be the class of (5) for episode $k$. Then $\mathcal Q$ has an $\varepsilon$-net in $\|\cdot\|_\infty$ (a finite subset of $\mathcal Q$) with at most
--   $$
--   2\Big(1+\frac{8H\sqrt{dk}}{\varepsilon}\Big)^d\Big(1+\frac{8\max\{\beta^2,\beta^4\}\sqrt d}{\varepsilon^2}\Big)^{d^2}
--   $$
--   elements; that is, the $\varepsilon$-covering number satisfies $\mathcal N_\varepsilon\le2(1+8H\sqrt{dk}/\varepsilon)^d(1+8\max\{\beta^2,\beta^4\}\sqrt d/\varepsilon^2)^{d^2}$. For $\beta\le1$ this is the printed bound.
--
--   With $\beta=c\,dH\sqrt\iota$ and $\varepsilon=1/(KH)$ this gives $\log\mathcal N_\varepsilon\lesssim d^2(\iota+\log c)$, the size of the union bound in Lemma 2.
--
--   Differences from the source:
--   - reading: the ε-covering number 𝒩_ε of 𝒬 → the existence of an ε-net contained in 𝒬 with at most the stated number of elements; reason: an internal net is the convention of the cited covering bound (Vershynin 2012, Lemma 5.2) and is what Algorithm 2 rounds into; it implies the bound for external covers
--   - correction: N_ε ≤ 2(1 + 8H√(dk)/ε)^d (1 + 8β²√d/ε²)^{d²} → the same bound with max{β², β⁴} in place of β²; reason: the printed bound is false for large β: d = k = 1, 𝒮 = {s, t}, one action, φ(s) = 1, φ(t) = −1, H = 40000, β = 200, ε = 2000; every (u, v) ∈ [−H, H]² equals (Q(s), Q(t)) for some Q ∈ 𝒬 (ρ = sign(u + v), w = (u − v)/2, A = ((u + v)/(2β))² ≤ β²), so 𝒩_ε ≥ (H/ε)² = 400, while the printed bound is 2·161·1.08 ≈ 347.8; the proof (p.29) drops the factor β in |ρβ√(φᵀAφ) − ρβ√(φᵀA′φ)| ≤ √|φᵀ(A − A′)φ|, and restoring it makes the A-cover scale ε²/(4β²), which gives β⁴; for β ≤ 1 the printed β² is kept, since it follows from the corrected proof
-- source:
--   Xie, Chen, Wang & Yang, Learning Zero-Sum Simultaneous-Move Markov Games Using Function Approximation and Correlated Equilibrium, arXiv:2002.07066v3, Lemma 11, p.29

import Mathlib
import Definitions.Def_LinearZeroSumMG_QClass
import Definitions.Def_LinearZeroSumMG_IsEpsNet

namespace LinearZeroSumMG

/-- **Lemma 11 (Covering), corrected: `max{β², β⁴}` in place of `β²`.**
Xie, Chen, Wang & Yang, *Learning Zero-Sum Simultaneous-Move Markov Games Using Function
Approximation and Correlated Equilibrium*, arXiv:2002.07066v3, Lemma 11, p.29: "The `ε`-covering
number of `𝒬` with respect to the `ℓ∞` norm satisfies
`𝒩_ε ≤ 2(1 + 8H√(dk)/ε)^d (1 + 8β²√d/ε²)^{d²}`."

For every feature map `φ` with `‖φ(x, a, b)‖ ≤ 1`, every `H, k ∈ ℕ`, `β > 0` and `ε > 0`, the class
`𝒬` of (5) for episode `k` has an `ε`-net (in `‖·‖_∞`, contained in `𝒬`) with at most
`2(1 + 8H√(dk)/ε)^d (1 + 8 max{β², β⁴}√d/ε²)^{d²}` elements.

**Formalization Note**
- "`𝒩_ε ≤ B`" is stated as the existence of an `ε`-net with at most `B` elements. The net is
  internal (a subset of `𝒬`).
- **Correction.** The printed bound, with `β²` in the second factor, is false when `β > 1` is
  large: take `d = k = 1`, `𝒮 = {s, t}`, one action, `φ(s) = 1`, `φ(t) = −1`, `H = 40000`,
  `β = 200`, `ε = 2000`. Every pair `(u, v) ∈ [−H, H]²` is `(Q(s), Q(t))` for some `Q ∈ 𝒬`
  (`ρ = sign(u + v)`, `w = (u − v)/2`, `A = ((u + v)/(2β))²` ≤ `β²`), so `𝒩_ε ≥ (H/ε)² = 400`, while the
  printed bound is `2 · 161 · 1.08 ≈ 347.8`. The proof (p.29) bounds
  `|ρβ√(φᵀAφ) − ρβ√(φᵀA'φ)|` by `√|φᵀ(A − A')φ|`, dropping the factor `β`; with it, the cover of
  `{‖A‖_F ≤ β²√d}` must have scale `ε²/(4β²)`, which gives `(1 + 8β⁴√d/ε²)^{d²}`. The statement
  keeps the printed `β²` when `β ≤ 1` (where it follows from the corrected proof) and uses `β⁴`
  when `β > 1`, i.e. `max{β², β⁴}`. -/
theorem lemma_11 {S A : Type*} {d : ℕ} (φ : S → A → A → Fin d → ℝ)
    (hφ : ∀ x a b, ApproxVI.euclNorm (φ x a b) ≤ 1) (H k : ℕ) (β ε : ℝ) (hβ : 0 < β) (hε : 0 < ε) :
    ∃ N : Finset (S → A → A → ℝ), IsEpsNet N (QClass φ H β k) ε ∧
      (N.card : ℝ) ≤ 2 * (1 + 8 * H * Real.sqrt (d * k) / ε) ^ d *
        (1 + 8 * max (β ^ 2) (β ^ 4) * Real.sqrt d / ε ^ 2) ^ (d ^ 2) := by sorry

end LinearZeroSumMG
