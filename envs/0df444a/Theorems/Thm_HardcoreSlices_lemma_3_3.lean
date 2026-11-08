-- Prove2me | Theorems.Thm_HardcoreSlices_lemma_3_3
-- name    : HardcoreSlices.lemma_3_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T06:37:02.183195+00:00
-- url     : https://prove2.me/theorems/baf6827a-11ef-4ef1-af20-b948b385bbde
-- title:
--   Lemma 3.3 — concentration of $|N(\tau)|$ in the pairing model
-- statement:
--   In the bipartite pairing model with sides of size $m\ge1$ and $\Delta\ge2$, let $\tau\subseteq X$ and $t>0$. With $v=\frac14\bigl(1-(1-\frac{\Delta-1}{\Delta m})^2\bigr)^{-1}$,
--   $$\Pr\bigl[\bigl||N(\tau)|-\mathbf E|N(\tau)|\bigr|>t\bigr]\le2\exp\Bigl(-\frac{t^2}{2(v+t/3)}\Bigr).$$
--   Moreover there is a nonnegative sequence $\omega(\Delta)\to0$, chosen first, such that for $m\ge\Delta$,
--   $$\Pr\bigl[\bigl||N(\tau)|-\mathbf E|N(\tau)|\bigr|>t\bigr]\le2\exp\Bigl(-\frac12\cdot\frac{t^2}{(\frac18+\omega(\Delta))|Y|+t/3}\Bigr).$$
--   This concentration, with a union bound over sets $\tau$, gives Lemma 3.1.
--
--   Differences from the source:
--   - generalization: the bound with (1/8 + o∆(1))|Y| → also the sharper bound with the explicit variance v of p.14, for every m ≥ 1; reason: the printed bound follows from v ≤ (1/8 + ω)m
--   - reading: o∆(1), any |Y| → a nonnegative sequence ω(Δ) → 0 and m ≥ Δ; reason: the proof concerns |Y| → ∞ at fixed ∆; v ≤ (1/8 + o∆(1))|Y| has no support for m < Δ
-- source:
--   Kocurek, Oveis Gharan, Tjowasi, Sampling from the Hardcore Model on Random Regular Bipartite Graphs above the Uniqueness Threshold, arXiv:2604.21847 (version held, sha256 363c225d…), Lemma 3.3, p.13; display on p.14

import Mathlib
import Definitions.Def_HardcoreSlices_pairingNbr

open Classical Filter

namespace HardcoreSlices

/-- **Lemma 3.3.** Kocurek, Oveis Gharan, Tjowasi, *Sampling from the Hardcore Model on Random Regular Bipartite Graphs above the Uniqueness Threshold*, arXiv:2604.21847 (version held, sha256 363c225d…), p.13: "For any `t > 0`, we have
`Pr[ | |N(τ)| − E|N(τ)| | > t ] ≤ 2 exp( −(1/2) · t² / ( (1/8 + o∆(1))|Y| + t/3 ) )`."
The setting is the bipartite pairing model (Proposition 3.2, p.13).

**Formalization Note.** The first clause is the sharper bound of the proof, with the explicit variance `pairingVariance m Δ` of the
display on p.14, for every `m ≥ 1`. The second clause is the printed form, where `o∆(1)` is a nonnegative sequence `ω` tending to `0`, chosen
before `∆`, `m`, `τ`, `t`. It is stated for `m ≥ Δ`, as the proof concerns `|Y| → ∞` at fixed `∆`. -/
theorem lemma_3_3 :
    ∃ ω : ℕ → ℝ, (∀ Δ, 0 ≤ ω Δ) ∧ Tendsto ω atTop (nhds 0) ∧
      ∀ Δ : ℕ, 2 ≤ Δ → ∀ m : ℕ, 1 ≤ m → ∀ τ : Finset (Fin m), ∀ t : ℝ, 0 < t →
        (pairingProb (fun π : Equiv.Perm (Fin m × Fin Δ) =>
            t < |((pairingNbr π τ).card : ℝ) - pairingMeanNbr (Δ := Δ) τ|) ≤
          2 * Real.exp (-(t ^ 2 / (2 * (pairingVariance m Δ + t / 3))))) ∧
        (Δ ≤ m → pairingProb (fun π : Equiv.Perm (Fin m × Fin Δ) =>
            t < |((pairingNbr π τ).card : ℝ) - pairingMeanNbr (Δ := Δ) τ|) ≤
          2 * Real.exp (-(1 / 2) * (t ^ 2 / ((1 / 8 + ω Δ) * m + t / 3)))) := by sorry

end HardcoreSlices
