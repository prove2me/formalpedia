-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_sum_apply_weylPrime3_mul_radicalP21_mul_iotaGL_eq_zero_of_level
-- name    : LanglandsTunnell.CubicInduction.sum_apply_weylPrime3_mul_radicalP21_mul_iotaGL_eq_zero_of_level
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.012626+00:00
-- url     : https://prove2.me/theorems/d2ecf10f-d3a8-52cd-832f-d1018958bc80
-- title:
--   Vanishing of middle-cell sums for deeply ramified I(χ) vectors
-- statement:
--   Let $v$ be a height-one prime of $\mathcal{O}_{\mathbb{Q}}$, write $F=\mathbb{Q}_v$ for the $v$-adic completion with valuation $\mathrm{val}$ taking values in $\mathbb{Z}_{\ge 0}^{\times}\cup\{0\}$ written multiplicatively via `WithZero.exp`, let $\chi=(\chi_0,\chi_1,\chi_2)$ be monoid homomorphisms $F^{\times}\to\mathbb{C}^{\times}$ and let $b\in\mathbb{N}$ be such that each $\chi_i$ is non-trivial on some element of `higherUnitsAt ℚ v b`, i.e. on some unit $u$ with $\mathrm{val}(u)=1$ and, unless $b=0$, $\mathrm{val}(u-1)\le\exp(-b)$. Let $\Phi:GL_3(F)\to\mathbb{C}$ lie in `principalSeries3 v χ`: $\Phi$ is locally constant, invariant under left translation by the upper unipotent matrices `upperUnipotent3 x y z`, and satisfies $\Phi(\mathrm{diag}(a_0,a_1,a_2)g)=\bigl(\prod_i\chi_i(a_i)\bigr)\,(\|a_0\|/\|a_2\|)\,\Phi(g)$ for $a_i\in F^{\times}$. Assume further that $\Phi$ is invariant under right translation by $\iota(\mathrm{diag}(u,1))=\mathrm{diag}(u,1,1)$ for every $u$ with $\mathrm{val}(u)=1$, by the matrices `upperUnipotent3 s 0 0` and `lowerUnipotent21 s` (unipotent with $(1,2)$-, resp. $(2,1)$-entry $s$) for all $s$ with $\mathrm{val}(s)\le\exp(-b)$, and, for some $m\in\mathbb{N}$, by every $\kappa\in GL_3(F)$ all of whose entries satisfy $\mathrm{val}(\kappa_{ij}-\delta_{ij})\le\exp(-m)$. Let $k\in GL_2(F)$ have all entries of $k$ and of $k^{-1}$ of valuation $\le 1$, and write $\iota(k)=\mathrm{diag}(k,1)$, $w=$ `weylPrime3` the permutation matrix interchanging the second and third basis vectors, and $n(y)=$ `radicalP21 ![0, y]` the unipotent matrix with $(2,3)$-entry $y$ and no other off-diagonal entry. Then two things hold: first, $\Phi(w\,n(y)\,\iota(k))=0$ whenever $\exp(m)\le\mathrm{val}(y)$; second, for every $c\in\mathbb{N}$ with $m\le c$ and every finite set $S\subseteq F$ with $\mathrm{val}(s)\le\exp(c)$ for all $s\in S$ and such that each $y$ with $\mathrm{val}(y)\le\exp(c)$ admits exactly one $s\in S$ with $\mathrm{val}(y-s)\le\exp(-m)$, one has $\sum_{s\in S}\Phi(w\,n(s)\,\iota(k))=0$.
--
--   This is the contribution of the middle Bruhat double coset $Bw P$, for $P$ the standard parabolic of type $(2,1)$, to the geometric-lemma computation of the Jacquet module of the principal series $I(\chi)$ of $GL_3(F)$: the Riemann sums in the second clause compute the relevant integral over the $(2,3)$-radical, and they vanish because the resulting $GL_2$-vector lies in a principal series whose characters are too deeply ramified to support a level-$b$ fixed vector on $GL_2(\mathcal{O})$. It feeds the construction of the linear functional vanishing on translates along `radicalP21` in [`LanglandsTunnell.CubicInduction.exists_forall_linearMap_apply_eq_zero_of_radicalP21_of_mem_principalSeries3`](thm.html#LanglandsTunnell.CubicInduction.exists_forall_linearMap_apply_eq_zero_of_radicalP21_of_mem_principalSeries3).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_sum_apply_weylPrime3_mul_radicalP21_mul_iotaGL_eq_zero_of_level.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries3
import Definitions.Def_LanglandsTunnell_CubicInduction_GlobalZeta31

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField

theorem LanglandsTunnell.CubicInduction.sum_apply_weylPrime3_mul_radicalP21_mul_iotaGL_eq_zero_of_level
    (v : HeightOneSpectrum (𝓞 ℚ)) (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (b : ℕ)
    (hχ : ∀ i, ∃ u ∈ LanglandsTunnell.TateLocal.higherUnitsAt ℚ v b, χ i u ≠ 1)
    (Φ : LanglandsTunnell.CubicInduction.LocalGL3 v → ℂ)
    (hΦ : Φ ∈ LanglandsTunnell.CubicInduction.principalSeries3 v χ)
    (hdiag : ∀ (g : LanglandsTunnell.CubicInduction.LocalGL3 v) (u : (v.adicCompletion ℚ)ˣ),
      Valued.v (u : v.adicCompletion ℚ) = 1 →
      Φ (g * LanglandsTunnell.CubicInduction.iotaGL (LanglandsTunnell.CubicInduction.diagUnitGL2 u)) = Φ g)
    (hupper : ∀ (g : LanglandsTunnell.CubicInduction.LocalGL3 v) (s : v.adicCompletion ℚ),
      Valued.v s ≤ WithZero.exp (-(b : ℤ)) →
      Φ (g * LanglandsTunnell.CubicInduction.upperUnipotent3 s 0 0) = Φ g)
    (hlower : ∀ (g : LanglandsTunnell.CubicInduction.LocalGL3 v) (s : v.adicCompletion ℚ),
      Valued.v s ≤ WithZero.exp (-(b : ℤ)) →
      Φ (g * LanglandsTunnell.CubicInduction.lowerUnipotent21 s) = Φ g)
    (m : ℕ)
    (hm : ∀ κ : LanglandsTunnell.CubicInduction.LocalGL3 v,
      (∀ i j, Valued.v ((κ : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j -
        (1 : Matrix (Fin 3) (Fin 3) (v.adicCompletion ℚ)) i j) ≤ WithZero.exp (-(m : ℤ))) →
      ∀ g : LanglandsTunnell.CubicInduction.LocalGL3 v, Φ (g * κ) = Φ g)
    (k : GL (Fin 2) (v.adicCompletion ℚ))
    (hk : ∀ i j, Valued.v ((k : GL (Fin 2) (v.adicCompletion ℚ)) i j) ≤ 1)
    (hkinv : ∀ i j, Valued.v ((k⁻¹ : GL (Fin 2) (v.adicCompletion ℚ)) i j) ≤ 1) :
    (∀ y : v.adicCompletion ℚ, WithZero.exp (m : ℤ) ≤ Valued.v y →
      Φ (LanglandsTunnell.CubicInduction.weylPrime3 * LanglandsTunnell.CubicInduction.radicalP21 ![0, y] *
        LanglandsTunnell.CubicInduction.iotaGL k) = 0) ∧
    ∀ (c : ℕ) (S : Finset (v.adicCompletion ℚ)), m ≤ c →
      (∀ s ∈ S, Valued.v s ≤ WithZero.exp (c : ℤ)) →
      (∀ y : v.adicCompletion ℚ, Valued.v y ≤ WithZero.exp (c : ℤ) →
        ∃! s, s ∈ S ∧ Valued.v (y - s) ≤ WithZero.exp (-(m : ℤ))) →
      ∑ s ∈ S, Φ (LanglandsTunnell.CubicInduction.weylPrime3 * LanglandsTunnell.CubicInduction.radicalP21 ![0, s] *
        LanglandsTunnell.CubicInduction.iotaGL k) = 0 := by sorry
