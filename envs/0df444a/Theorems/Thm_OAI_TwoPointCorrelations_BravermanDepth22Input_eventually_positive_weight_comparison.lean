-- Prove2me | Theorems.Thm_OAI_TwoPointCorrelations_BravermanDepth22Input_eventually_positive_weight_comparison
-- name    : OAI.TwoPointCorrelations.BravermanDepth22Input.eventually_positive_weight_comparison
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T01:12:19.017683+00:00
-- url     : https://prove2.me/theorems/b13cf41c-59be-4f85-8580-8448f11b0b90
-- title:
--   Under Braverman's theorem, a long interval fools circuit-gated positive prime tables of residues
-- statement:
--   Assume `BravermanDepth22Input` (Braverman's theorem for depth-22 AC⁰ circuits). Then there is a natural $A\ge1000$ such that for all sufficiently large $L$: let $1\le m\le e^L+1$ and let $s_1,\dots,s_m$ be pairwise coprime nonzero naturals each at most $e^L$; let $t,r,N_{\mathrm{in}}$ be naturals and $p_1,\dots,p_t\ge1$ with $t\le L^2$ and $r\le100\log L$; let `coord`, the Boolean residue tests, `pindex` and an AC⁰ circuit $c$ on $N_{\mathrm{in}}$ inputs of depth at most $19$ and size at most $e^{L^3}$ be given. For $z\in\prod_j\mathbb Z/s_j$ let $\mathrm{bits}(z)$ = `residueCircuitInputs s coord test z` and
--   $$F(z)=\texttt{positivePrimeTable}\ p\ r\ (\mathrm{bits}(z)\circ\mathrm{pindex})\cdot\mathbf 1_c(\mathrm{bits}(z)).$$
--   Then for all naturals $a$ and $N\ge\exp(L^A/2)$,
--   $$\Big|\frac1N\sum_{x<N}F\big((a+x)\bmod s_j\big)_j-\mathbb E_zF(z)\Big|\le e^{-L^9}.$$
-- source:
--   OpenAI, Ordinary two-point correlations of multiplicative functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/main/preprints/Ordinary-two-point-correlations-of-multiplicative-functions-September-24-2026/final.pdf; Lean: lean/OAI/NumberTheory/TwoPoint, Apache License 2.0); Lean declaration `OAI.TwoPointCorrelations.BravermanDepth22Input.eventually_positive_weight_comparison`

import Mathlib
import Definitions.Def_OAIChowlaTwoPointDefs

namespace OAI.TwoPointCorrelations

open Finset
open Filter
open scoped Classical

theorem BravermanDepth22Input.eventually_positive_weight_comparison
    (hBr : BravermanDepth22Input) :
    ∃ A : ℕ, 1000 ≤ A ∧ ∀ᶠ L : ℝ in atTop,
      ∀ (m : ℕ) (s : Fin m → ℕ) [∀ i, NeZero (s i)],
      0 < m → (m : ℝ) ≤ Real.exp L + 1 →
      Pairwise (fun i j => (s i).Coprime (s j)) →
      (∀ i, (s i : ℝ) ≤ Real.exp L) →
      ∀ (t r Ninput : ℕ) (p : Fin t → ℕ),
      (∀ i, 1 ≤ p i) → (t : ℝ) ≤ L ^ 2 → (r : ℝ) ≤ 100 * Real.log L →
      ∀ (coord : Fin Ninput → Fin m)
        (test : ∀ i, ZMod (s (coord i)) → Bool) (pindex : Fin t → Fin Ninput)
        (c : AC0Circuit Ninput), c.depth ≤ 19 → (c.size : ℝ) ≤ Real.exp (L ^ 3) →
      ∀ a N : ℕ, Real.exp (L ^ A / 2) ≤ (N : ℝ) →
      let F := fun z : ∀ j, ZMod (s j) =>
        let bits := residueCircuitInputs s coord test z
        positivePrimeTable p r (fun i => bits (pindex i)) * c.indicator bits
      |uniformAverage (fun x : Fin N => F (fun j => (a + x.val : ZMod (s j)))) -
        uniformAverage F| ≤ Real.exp (-(L ^ 9)) := by
  sorry

end OAI.TwoPointCorrelations
