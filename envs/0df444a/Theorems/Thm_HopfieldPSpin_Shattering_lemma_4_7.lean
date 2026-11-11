-- Prove2me | Theorems.Thm_HopfieldPSpin_Shattering_lemma_4_7
-- name    : HopfieldPSpin.Shattering.lemma_4_7
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T19:08:42.578027+00:00
-- url     : https://prove2.me/theorems/1ad2483b-1911-4f50-ace2-1cf9d8f073ab
-- title:
--   Lemma 4.7 — $|Y|\mathbf 1_{E_1}\le U_n=2L^pn^{p/2}/\sqrt{p!}$
-- statement:
--   For $Y=X_1(\sigma)$ or $Y=X_1(\sigma)+X_1(\tau)$,
--   $$|Y|\,\mathbf 1_{E_1}\le U_n,\qquad U_n=\frac{2L^pn^{p/2}}{\sqrt{p!}},\quad L=2 .$$
--   A deterministic bound, valid for every realization of the patterns.
--
--   Differences from the source:
--   - encoding: spins $\sigma\in\{-1,1\}^n$, patterns $k=1,\dots,M$, coordinates $i=1,\dots,n$ → `Config n = Fin n → ℤˣ` (the units of ℤ are exactly ±1), patterns `Fin M`, coordinates `Fin n` (0-based); reason: Lean convention; the same configurations and indices
--   - generalization: pattern index $k=1$ ($X_1$, $E_1$) → every pattern index $k$ ($X_k$, $E_k$); reason: the bound is the same for every pattern; $k=1$ (Lean index 0) is an instance
-- source:
--   Kızıldağ, Şahin, Hopfield Model with p-spin Interactions: Shattering, Disorder Chaos and Sampling Hardness, STOC 2027 submission (manuscript sha256 4bbdc838…), p. 19 (PDF 21), Lemma 4.7, (4.12)

import Mathlib
import Definitions.Def_HopfieldPSpin_Shattering_Model

namespace HopfieldPSpin.Shattering

/-- Lemma 4.7 (p. 19): for `Y = X_k(σ)` or `Y = X_k(σ) + X_k(τ)`, `|Y| 1_{E_k} ≤ U_n`,
`U_n = 2 L^p n^{p/2} / √(p!)` (stated for every pattern index `k`; the source states `k = 1`). -/
theorem lemma_4_7 (n M p : ℕ) (hp : 3 ≤ p) (hn : p ≤ n) (η : Fin M → Fin n → ℝ) (k : Fin M)
    (σ τ : Config n) :
    |patternField n M p η k σ| * (normEvent n M k).indicator (fun _ => (1 : ℝ)) η ≤ bigU n p ∧
    |patternField n M p η k σ + patternField n M p η k τ| *
        (normEvent n M k).indicator (fun _ => (1 : ℝ)) η ≤ bigU n p := by sorry

end HopfieldPSpin.Shattering
