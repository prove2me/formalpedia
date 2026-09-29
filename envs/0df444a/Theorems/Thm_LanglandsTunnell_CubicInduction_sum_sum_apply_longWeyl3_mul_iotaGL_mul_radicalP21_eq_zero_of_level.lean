-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_sum_sum_apply_longWeyl3_mul_iotaGL_mul_radicalP21_eq_zero_of_level
-- name    : LanglandsTunnell.CubicInduction.sum_sum_apply_longWeyl3_mul_iotaGL_mul_radicalP21_eq_zero_of_level
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.012626+00:00
-- url     : https://prove2.me/theorems/833537b3-e4dc-57a4-9809-29e046a637fe
-- title:
--   Open-cell sums vanish for level-fixed GL₃ principal series vectors
-- statement:
--   Fix a finite place $v$ of $\mathbb{Q}$ (a height-one prime of $\mathcal{O}_{\mathbb{Q}}$), write $F = \mathbb{Q}_v$ for the adic completion, let $\chi_0,\chi_1,\chi_2 : F^\times \to \mathbb{C}^\times$ be characters and $b \in \mathbb{N}$, and assume each $\chi_i$ is non-trivial on the set of units $u$ with $\mathrm{v}(u)=1$ and ($b=0$ or $\mathrm{v}(u-1)\le \exp(-b)$). Let $\Psi : GL_3(F)\to\mathbb{C}$ lie in `principalSeries3`, i.e. $\Psi$ is locally constant, invariant under left translation by the upper unipotent matrices `upperUnipotent3` $x\,y\,z$, and satisfies $\Psi(\mathrm{diag}(a_0,a_1,a_2)g) = \chi_0(a_0)\chi_1(a_1)\chi_2(a_2)\,(\lVert a_0\rVert/\lVert a_2\rVert)\,\Psi(g)$. Assume $\Psi$ is right invariant under $\iota(\mathrm{diag}(u,1))=\mathrm{diag}(u,1,1)$ for $\mathrm{v}(u)=1$, under `upperUnipotent3` $s\,0\,0$ and under `lowerUnipotent21` $s$ for $\mathrm{v}(s)\le\exp(-b)$, and, for some $m\in\mathbb{N}$, under every $\kappa\in GL_3(F)$ with all entries of $\kappa - 1$ of valuation $\le \exp(-m)$. Assume further that $\Psi(s_2\,n\,\iota(k'))=0$ for all $k'$ with $k'$ and $k'^{-1}$ integral, where $s_2$ is the permutation matrix `weylPrime3` swapping the last two coordinates and $n$ is the unipotent matrix with $(0,2)$-entry $0$ and $(1,2)$-entry $y$, $y\in F$ arbitrary. Finally let $k\in GL_2(F)$ with $k$ and $k^{-1}$ integral. Then, with $w_3$ the antidiagonal permutation matrix `longWeyl3` and $\mathrm{rad}(Y)$ the unipotent matrix with $(0,2)$-entry $Y_0$ and $(1,2)$-entry $Y_1$: (1) $\Psi(w_3\,\iota(k)\,\mathrm{rad}(Y))=0$ for every $Y : \mathrm{Fin}\,2\to F$ with $\exp(m)\le\max(\mathrm{v}(Y_0),\mathrm{v}(Y_1))$; and (2) for every $c\in\mathbb{N}$ with $m\le c$ and every finite set $S\subseteq F$ whose elements have valuation $\le\exp(c)$ and which contains, for each $y$ with $\mathrm{v}(y)\le\exp(c)$, a unique $s$ with $\mathrm{v}(y-s)\le\exp(-m)$, one has $\sum_{s\in S}\sum_{s'\in S}\Psi(w_3\,\iota(k)\,\mathrm{rad}(s,s'))=0$.
--
--   This is the contribution of the open Bruhat double coset $B w_3 P$, for the standard parabolic $P$ of type $(2,1)$, to the geometric-lemma computation of the Jacquet module of a principal series of $GL_3(F)$: a vector fixed by a principal congruence subgroup and already vanishing on the smaller cells has vanishing open-cell orbital sums along the radical of $P$. It feeds into [`LanglandsTunnell.CubicInduction.exists_forall_linearMap_apply_eq_zero_of_radicalP21_of_mem_principalSeries3`](thm.html#LanglandsTunnell.CubicInduction.exists_forall_linearMap_apply_eq_zero_of_radicalP21_of_mem_principalSeries3), and the argument uses the $GL_2$ vanishing statement `eq_zero_of_valuation_le_one_of_diagUnits2_mul_of_mul_level` together with `apply_eq_zero_of_apply_two_eq_zero_of_mem_principalSeries3_of_level`.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_sum_sum_apply_longWeyl3_mul_iotaGL_mul_radicalP21_eq_zero_of_level.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries3
import Definitions.Def_LanglandsTunnell_CubicInduction_GlobalZeta31

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField

theorem LanglandsTunnell.CubicInduction.sum_sum_apply_longWeyl3_mul_iotaGL_mul_radicalP21_eq_zero_of_level
    (v : HeightOneSpectrum (𝓞 ℚ)) (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (b : ℕ)
    (hχ : ∀ i, ∃ u ∈ LanglandsTunnell.TateLocal.higherUnitsAt ℚ v b, χ i u ≠ 1)
    (Ψ : LanglandsTunnell.CubicInduction.LocalGL3 v → ℂ)
    (hΨ : Ψ ∈ LanglandsTunnell.CubicInduction.principalSeries3 v χ)
    (hdiag : ∀ (g : LanglandsTunnell.CubicInduction.LocalGL3 v) (u : (v.adicCompletion ℚ)ˣ),
      Valued.v (u : v.adicCompletion ℚ) = 1 →
      Ψ (g * LanglandsTunnell.CubicInduction.iotaGL (LanglandsTunnell.CubicInduction.diagUnitGL2 u)) = Ψ g)
    (hupper : ∀ (g : LanglandsTunnell.CubicInduction.LocalGL3 v) (s : v.adicCompletion ℚ),
      Valued.v s ≤ WithZero.exp (-(b : ℤ)) →
      Ψ (g * LanglandsTunnell.CubicInduction.upperUnipotent3 s 0 0) = Ψ g)
    (hlower : ∀ (g : LanglandsTunnell.CubicInduction.LocalGL3 v) (s : v.adicCompletion ℚ),
      Valued.v s ≤ WithZero.exp (-(b : ℤ)) →
      Ψ (g * LanglandsTunnell.CubicInduction.lowerUnipotent21 s) = Ψ g)
    (m : ℕ)
    (hm : ∀ κ : LanglandsTunnell.CubicInduction.LocalGL3 v,
      (∀ i j, Valued.v ((κ : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j -
        (1 : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j) ≤ WithZero.exp (-(m : ℤ))) →
      ∀ g : LanglandsTunnell.CubicInduction.LocalGL3 v, Ψ (g * κ) = Ψ g)
    (hmid : ∀ k' : GL (Fin 2) (v.adicCompletion ℚ),
      (∀ i j, Valued.v ((k' : GL (Fin 2) (v.adicCompletion ℚ)) i j) ≤ 1) →
      (∀ i j, Valued.v ((k'⁻¹ : GL (Fin 2) (v.adicCompletion ℚ)) i j) ≤ 1) →
      ∀ y : v.adicCompletion ℚ,
        Ψ (LanglandsTunnell.CubicInduction.weylPrime3 * LanglandsTunnell.CubicInduction.radicalP21 ![0, y] *
          LanglandsTunnell.CubicInduction.iotaGL k') = 0)
    (k : GL (Fin 2) (v.adicCompletion ℚ))
    (hk : ∀ i j, Valued.v ((k : GL (Fin 2) (v.adicCompletion ℚ)) i j) ≤ 1)
    (hkinv : ∀ i j, Valued.v ((k⁻¹ : GL (Fin 2) (v.adicCompletion ℚ)) i j) ≤ 1) :
    (∀ Y : Fin 2 → v.adicCompletion ℚ, WithZero.exp (m : ℤ) ≤ max (Valued.v (Y 0)) (Valued.v (Y 1)) →
      Ψ (LanglandsTunnell.CubicInduction.longWeyl3 * LanglandsTunnell.CubicInduction.iotaGL k *
        LanglandsTunnell.CubicInduction.radicalP21 Y) = 0) ∧
    ∀ (c : ℕ) (S : Finset (v.adicCompletion ℚ)), m ≤ c →
      (∀ s ∈ S, Valued.v s ≤ WithZero.exp (c : ℤ)) →
      (∀ y : v.adicCompletion ℚ, Valued.v y ≤ WithZero.exp (c : ℤ) →
        ∃! s, s ∈ S ∧ Valued.v (y - s) ≤ WithZero.exp (-(m : ℤ))) →
      ∑ s ∈ S, ∑ s' ∈ S, Ψ (LanglandsTunnell.CubicInduction.longWeyl3 * LanglandsTunnell.CubicInduction.iotaGL k *
        LanglandsTunnell.CubicInduction.radicalP21 ![s, s']) = 0 := by sorry
