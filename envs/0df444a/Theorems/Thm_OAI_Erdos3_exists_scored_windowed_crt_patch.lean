-- Prove2me | Theorems.Thm_OAI_Erdos3_exists_scored_windowed_crt_patch
-- name    : OAI.Erdos3.exists_scored_windowed_crt_patch
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-09T00:25:19.428677+00:00
-- url     : https://prove2.me/theorems/a7317a23-cd15-40c1-b233-ce2a8376791a
-- title:
--   A windowed positive cyclic niltest score on a CRT product yields a scored polynomial patch
-- statement:
--   Let $s \ge 1$ be a natural number (and $u$ a universe level, a parameter of the theorem). Then there is a natural number $C \ge 2$ such that the following holds. Let $J$ be a finite type with decidable equality, $N : J \to \mathbb{N}$ pairwise coprime positive moduli with $M = \prod_j N_j > 0$, and $\pi : \mathbb{Z}/M \to \prod_j \mathbb{Z}/N_j$ the Chinese-remainder isomorphism `ZMod.prodEquivPi N hN`. Let $T : \mathbb{Z}/M \to \mathbb{R}$, let $w$ be a `RepresentativeWindow` (OpenAI's structure of a center $c \in \mathbb{R}$ and a $\mathrm{lip}$-Lipschitz function $\mathrm{value} : \mathbb{R} \to [0,1]$ that vanishes outside $(0,1)$ and outside $|x - c| < 1/4$), let $a : \prod_j \mathbb{Z}/N_j \to \mathbb{R}$ and $p \in \mathbb{R}$. Assume $0 \le p$; `PositiveCyclicNiltest s M p T` (OpenAI's predicate: $T(x) = \mathrm{Re}\,T'(x)$ for some unit-interval-valued niltest $T'$ of complexity at most $p$ on a rational filtered nilmanifold of degree at most $s$ whose Lie algebra lies in universe $u$); $\log(2 + w.\mathrm{lip}) \le p$; and
--   $$e^{-p} \le \mathbb{E}_{x \in \prod_j \mathbb{Z}/N_j}\, a(x)\, T(\pi^{-1}x)\, w.\mathrm{value}\bigl(\mathrm{val}(\pi^{-1}x)/M\bigr).$$
--   Then there exist $d \in \mathbb{N}$ and a `PolynomialPatch J s d` $P$ (OpenAI's structure bundling weights, a polynomial form and a kernel with Lipschitz constant $P.\mathrm{kernel.lip}$, evaluated by $P.\mathrm{value}$ on $\mathbb{R}^J$) such that $d + \log(2 + P.\mathrm{kernel.lip}) \le (p+2)^C$ and $\exp(-(p+2)^C) \le \mathbb{E}_{x}\, a(x)\, P.\mathrm{value}\bigl((\mathrm{val}(x_j))_j\bigr)$.
--
--   Lean: `OAI.Erdos3.exists_scored_windowed_crt_patch` in `lean/OAI/Combinatorics/Progressions/Lattices/ScoredCRTWindowPatch.lean` (OpenAI); the definitions it uses are in the definitions bundles `OAIErdos3B034` of this split (and the bundles they import).
-- source:
--   OpenAI, Quasipolynomial Bounds for Arithmetic Progressions, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Quasipolynomial-Bounds-for-Arithmetic-Progressions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/Progressions/Lattices/ScoredCRTWindowPatch.lean#L14

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B034

namespace OAI

section

namespace Erdos3

open scoped BigOperators

universe u

theorem exists_scored_windowed_crt_patch (s : ℕ) (hs : 1 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {J : Type*} [Fintype J] [DecidableEq J]
      (N : J → ℕ) [∀ j, NeZero (N j)] [NeZero (∏ j, N j)]
      (hN : Pairwise (fun i j => Nat.Coprime (N i) (N j)))
      (T : ZMod (∏ j, N j) → ℝ) (w : RepresentativeWindow)
      (a : ((j : J) → ZMod (N j)) → ℝ) {p : ℝ},
      0 ≤ p → PositiveCyclicNiltest.{u} s (∏ j, N j) p T →
      Real.log (2 + (w.lip : ℝ)) ≤ p →
      Real.exp (-p) ≤ (𝔼 x, (a x * T ((ZMod.prodEquivPi N hN).symm x)) *
        w.value ((((ZMod.prodEquivPi N hN).symm x).val : ℝ) / (∏ j, N j : ℕ))) →
      ∃ d : ℕ, ∃ P : PolynomialPatch J s d,
        (d : ℝ) + Real.log (2 + (P.kernel.lip : ℝ)) ≤ (p + 2) ^ C ∧
        Real.exp (-((p + 2) ^ C)) ≤ (𝔼 x, a x * P.value (fun j => ((x j).val : ℝ))) := by
  sorry

end Erdos3
end
end OAI
