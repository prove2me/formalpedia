-- Prove2me | Theorems.Thm_FourierSparseTesting1656_Uniform_lemma_4_1
-- name    : FourierSparseTesting1656.Uniform.lemma_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T06:33:36.729381+00:00
-- url     : https://prove2.me/theorems/74c9fed5-3e8d-4514-a553-1571f0664954
-- title:
--   Lemma 4.1 — one random sample list recovers every Boolean $s$-sparse function on $H$
-- statement:
--   Fix $d\ge0$ and an integer $s\ge1$, and let $H\le\mathbb F_2^n$ be a $d$-dimensional subspace with a complement $W$ of $H^\perp$ (which indexes the Fourier coefficients on $H$). There is an absolute constant $C_R>0$, independent of $n,d,s,H,W$, and for each such data a probability distribution on lists $h_1,\dots,h_q\in H$, not depending on any function values, all of whose lists have length
--   $$q\le C_R\,s\,(d+1)\log_2^2(2s),$$
--   such that Recover (Algorithm 2) run with such a list has the following two properties.
--
--   1. For every list and every $g:H\to\{-1,+1\}$, the output is Boolean and has at most $s$ nonzero Fourier coefficients.
--   2. With probability at least $9/10$ over the choice of the list, the output equals $g$ for every Boolean $g:H\to\{-1,+1\}$ with at most $s$ nonzero Fourier coefficients, simultaneously.
--
--   The quantifier order of the second property matters: one list is drawn and then serves every sparse $g$, so in the tester the failure probability is paid once for all cosets.
--
--   Differences from the source:
--
--   - reading: q = O(s(d+1) log² s) with log s (base 2), which is 0 at s = 1 → q ≤ C_R·s·(d+1)·log₂(2s)²; reason: log₂(2s) = 1 + log₂ s is the all-s reading: for s ≥ 2 it is within a factor 2 of log₂ s, and at s = 1 the literal bound would be 0 points, while the proof reads at least one point (p. 17)
--   - encoding: O(·) → one absolute constant C_R > 0 quantified before n, d, s, H and W; reason: the source's constant is absolute
--   - encoding: a distribution on lists h₁,…,h_q ∈ H → a PMF on lists of points of H (it may depend on n, d, s, H, W), with every list in its support of length at most the bound; probabilities via its outer measure; reason: the source's distribution is over lists in H and does not depend on function values
--   - encoding: Fix d ≥ 0 and H with dim H = d inside F₂ⁿ, W the complement of §2 → a subspace H ≤ (Fin n → ZMod 2) with finrank d and any complement W of H^⊥; reason: the setting of §4.1
--   - encoding: g : H → {−1,+1} and the output of Recover → bit functions H → Bool with false ↦ +1; sparsity counts nonzero coefficients indexed by W; reason: bijective encoding; same instances
-- source:
--   Arijit Ghosh, Manmatha Roy, STOC 2027 submission #1656 (October 2026), p. 16, Lemma 4.1 (Algorithm 2 and the full-table case, p. 17); PDF SHA256 5374116f8d05176f80f62c5fdaaddae029e1f9e6af853c5a8e1873cb4e83a123

import Mathlib
import Definitions.Def_FourierSparseTesting1656_Uniform_Recover

set_option autoImplicit false
open FourierDimTesting102.Quantum
open Classical

namespace FourierSparseTesting1656.Uniform

/-- Lemma 4.1, p.16: one absolute constant `C_R > 0` such that for every `d ≥ 0`, integer `s ≥ 1`
and `d`-dimensional `H ≤ F₂ⁿ` (with a complement `W` of `H^⊥`) there is a distribution on lists in
`H`, independent of all function values, of length at most `C_R s (d+1) log₂²(2s)`, such that
`Recover` (1) outputs a Boolean `s`-Fourier-sparse function for every list and every `g`, and
(2) with probability at least `9/10` over the list outputs `g` itself for every Boolean
`s`-Fourier-sparse `g` simultaneously. -/
theorem lemma_4_1 :
    ∃ C_R : ℝ, 0 < C_R ∧
      ∀ (n d s : ℕ), 1 ≤ s →
      ∀ (H W : Submodule (ZMod 2) (V n)), Module.finrank (ZMod 2) H = d →
        IsComplementOfPerp H W →
        ∃ μ : PMF (List H),
          (∀ L ∈ μ.support, (L.length : ℝ) ≤ C_R * s * (d + 1) * logTwoS s ^ 2) ∧
          (∀ (L : List H) (g : H → Bool),
            subSparsity H W (fun h => signOf (recover s H W L g h)) ≤ s) ∧
          ENNReal.ofReal (9 / 10) ≤
            μ.toOuterMeasure {L | ∀ g : H → Bool,
              subSparsity H W (fun h => signOf (g h)) ≤ s → recover s H W L g = g} := by sorry

end FourierSparseTesting1656.Uniform
