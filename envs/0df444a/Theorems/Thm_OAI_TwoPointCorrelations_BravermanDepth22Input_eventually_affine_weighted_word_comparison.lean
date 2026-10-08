-- Prove2me | Theorems.Thm_OAI_TwoPointCorrelations_BravermanDepth22Input_eventually_affine_weighted_word_comparison
-- name    : OAI.TwoPointCorrelations.BravermanDepth22Input.eventually_affine_weighted_word_comparison
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-08T01:13:06.175239+00:00
-- url     : https://prove2.me/theorems/b77d0ae9-af80-4fd6-a4fa-ae1897028446
-- title:
--   Under Braverman's theorem, a long progression fools bounded circuit-gated functions of residues
-- statement:
--   Assume `BravermanDepth22Input` (Braverman's theorem for depth-22 AC⁰ circuits, as defined in the bundle: polylogarithmically $t$-wise uniform densities fool such circuits). Then there is a natural $A\ge1000$ such that for all sufficiently large real $L$ the following holds.
--
--   Let $m\ge1$ with $m\le e^L+1$, and let $s_1,\dots,s_m$ be pairwise coprime nonzero naturals, each at most $e^L$. Let $R,n,t,N_{\mathrm{in}},M$ be naturals with $n\le e^L$, $M\le400\log L$, $R\le4L$, $t\le L^2$. Let `coord`$:\{1..N_{\mathrm{in}}\}\to\{1..m\}$ and, for each input bit $i$, a Boolean test on $\mathbb Z/s_{\mathrm{coord}(i)}$; let `qindex`, `pindex` select input bits; let $f$ be a real function of $R$ subsets of $\{1..n\}$ and of $t$ bits with $|f|\le e^{L^4}$ whenever each subset has at most $M$ elements; and let $c$ be an AC⁰ circuit on $N_{\mathrm{in}}$ inputs of depth at most $19$ and size at most $e^{L^3}$. For a residue vector $z\in\prod_j\mathbb Z/s_j$ let $\mathrm{bits}(z)$ be the input bits obtained by applying the tests (`residueCircuitInputs`), and define $F(z)=f(\dots)$ (evaluated on the active sets `activeState` read off the bits through `qindex` and on the bits selected by `pindex`) when every active set has at most $M$ elements and $c(\mathrm{bits}(z))$ is true, and $F(z)=0$ otherwise. Then for all naturals $a,l,N$ with $l$ coprime to every $s_i$ and $N\ge\exp(L^A/2)$,
--
--   $$\Big|\frac1N\sum_{x<N}F\big((a+lx)\bmod s_j\big)_j-\mathbb E_{z}F(z)\Big|\le e^{-L^9},$$
--
--   the last expectation uniform over $\prod_j\mathbb Z/s_j$.
-- source:
--   OpenAI, Ordinary two-point correlations of multiplicative functions, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/main/preprints/Ordinary-two-point-correlations-of-multiplicative-functions-September-24-2026/final.pdf; Lean: lean/OAI/NumberTheory/TwoPoint, Apache License 2.0); Lean declaration `OAI.TwoPointCorrelations.BravermanDepth22Input.eventually_affine_weighted_word_comparison`

import Mathlib
import Definitions.Def_OAIChowlaTwoPointDefs

namespace OAI.TwoPointCorrelations

open Finset
open Filter

theorem BravermanDepth22Input.eventually_affine_weighted_word_comparison
    (hBr : BravermanDepth22Input) :
    ∃ A : ℕ, 1000 ≤ A ∧ ∀ᶠ L : ℝ in atTop,
      ∀ (m : ℕ) (s : Fin m → ℕ) [∀ i, NeZero (s i)],
      0 < m → (m : ℝ) ≤ Real.exp L + 1 →
      Pairwise (fun i j => (s i).Coprime (s j)) →
      (∀ i, (s i : ℝ) ≤ Real.exp L) →
      ∀ (R n t Ninput M : ℕ), (n : ℝ) ≤ Real.exp L →
      (M : ℝ) ≤ 400 * Real.log L → (R : ℝ) ≤ 4 * L → (t : ℝ) ≤ L ^ 2 →
      ∀ (coord : Fin Ninput → Fin m)
        (test : ∀ i, ZMod (s (coord i)) → Bool)
        (qindex : Fin R → Fin n → Fin Ninput) (pindex : Fin t → Fin Ninput)
        (f : (Fin R → Finset (Fin n)) → BooleanCube t → ℝ) (c : AC0Circuit Ninput),
      (∀ b : (Fin R → boundedActiveStates n M) × BooleanCube t,
        |f (fun r => (b.1 r).val) b.2| ≤ Real.exp (L ^ 4)) →
      c.depth ≤ 19 → (c.size : ℝ) ≤ Real.exp (L ^ 3) →
      ∀ a l N : ℕ, (∀ i, l.Coprime (s i)) → Real.exp (L ^ A / 2) ≤ (N : ℝ) →
      let F := fun z : ∀ j, ZMod (s j) =>
        let bits := residueCircuitInputs s coord test z
        if (∀ r, (activeState (fun i => bits (qindex r i))).card ≤ M) ∧ c.eval bits = true
        then f (fun r => activeState (fun i => bits (qindex r i))) (fun i => bits (pindex i))
        else 0
      |uniformAverage (fun x : Fin N => F (fun j => (a + l * x.val : ZMod (s j)))) -
        uniformAverage F| ≤ Real.exp (-(L ^ 9)) := by
  sorry

end OAI.TwoPointCorrelations
