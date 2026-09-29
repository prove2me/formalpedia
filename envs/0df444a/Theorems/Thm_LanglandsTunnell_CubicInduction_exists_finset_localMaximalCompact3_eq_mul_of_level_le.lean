-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_exists_finset_localMaximalCompact3_eq_mul_of_level_le
-- name    : LanglandsTunnell.CubicInduction.exists_finset_localMaximalCompact3_eq_mul_of_level_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:04.547556+00:00
-- url     : https://prove2.me/theorems/fd6617bd-1990-5103-ac14-da558424aa18
-- title:
--   Finite level-n transversals modulo level-m congruence in GL₃
-- statement:
--   Let $v$ be a point of the height-one spectrum of $\mathcal O_{\mathbb Q} = \mathbb Z$, i.e. a finite place of $\mathbb Q$, and write $\mathbb Q_v$ for the $v$-adic completion, with its valuation $\mathrm{Valued.v}$ taking values in $\mathbb Z$ written multiplicatively via `WithZero.exp`. Let $n, m$ be natural numbers with $n \le m$ and $m \ge 1$. The assertion is that there is a finite set $S$ of elements of $\mathrm{GL}_3(\mathbb Q_v)$ with the following two properties. First, every $s \in S$ lies in `localMaximalCompact3`, that is, all entries of $s$ and all entries of $s^{-1}$ have valuation $\le 1$, and moreover each entry of $s$ differs from the corresponding entry of the identity matrix by an element of valuation $\le \exp(-n)$. Second, for every $k$ in `localMaximalCompact3` (so $k$ and $k^{-1}$ have entries of valuation $\le 1$) such that every entry of $k$ differs from the corresponding entry of the identity by an element of valuation $\le \exp(-n)$, there is exactly one $s$ with $s \in S$ for which $k = s\kappa$ for some $\kappa \in \mathrm{GL}_3(\mathbb Q_v)$ all of whose entries differ from those of the identity by elements of valuation $\le \exp(-m)$. Uniqueness is asserted for $s$ alone, not for the pair $(s,\kappa)$.
--
--   This is the statement that the level-$m$ congruence subgroup has finite index in the level-$n$ congruence subgroup of the integral points of $\mathrm{GL}_3$ over a non-archimedean completion of $\mathbb Q$, packaged as a finite set of left coset representatives; its proof uses the compactness of `localMaximalCompact3`. It supports the constructions of invariant functionals and of vectors of prescribed level in the local principal series of $\mathrm{GL}_3$ used in the cubic-induction step.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_exists_finset_localMaximalCompact3_eq_mul_of_level_le.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries3

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField

theorem LanglandsTunnell.CubicInduction.exists_finset_localMaximalCompact3_eq_mul_of_level_le
    (v : HeightOneSpectrum (𝓞 ℚ)) (n m : ℕ) (hnm : n ≤ m) (hm : 1 ≤ m) :
    ∃ S : Finset (LocalGL3 v),
      (∀ s ∈ S, s ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v ∧ ∀ i j : Fin 3,
        Valued.v (gl3Entry v s i j - (1 : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j)
          ≤ WithZero.exp (-(n : ℤ))) ∧
      ∀ k ∈ localMaximalCompact3 (𝓞 ℚ) ℚ v,
        (∀ i j : Fin 3,
          Valued.v (gl3Entry v k i j - (1 : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j)
            ≤ WithZero.exp (-(n : ℤ))) →
        ∃! s, s ∈ S ∧ ∃ κ : LocalGL3 v,
          (∀ i j : Fin 3,
            Valued.v (gl3Entry v κ i j - (1 : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j)
              ≤ WithZero.exp (-(m : ℤ))) ∧
          k = s * κ := by sorry
