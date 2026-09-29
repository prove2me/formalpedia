-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_forall_higherUnitsAt_eq_one_of_mem_principalSeries2_of_forall_mem_localLevelOne_pow
-- name    : LanglandsTunnell.CubicInduction.forall_higherUnitsAt_eq_one_of_mem_principalSeries2_of_forall_mem_localLevelOne_pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:06.047113+00:00
-- url     : https://prove2.me/theorems/f2e1c18e-b125-5488-826e-b6b31c11ee7a
-- title:
--   Conductor bound for the characters of a principal series
-- statement:
--   Fix a height-one prime $p$ of the ring of integers of $\mathbb{Q}$, a pair $\chi = (\chi_0,\chi_1)$ of multiplicative characters $(\mathbb{Q}_p)^{\times} \to \mathbb{C}^{\times}$ (where $\mathbb{Q}_p$ denotes the $p$-adic completion `p.adicCompletion ℚ`), a natural number $b$, and a function $f : \mathrm{GL}_2(\mathbb{Q}_p) \to \mathbb{C}$. Assume $f$ lies in `principalSeries2 p χ`, that is: $f$ is locally constant, $f\big(\left(\begin{smallmatrix}1&x\\0&1\end{smallmatrix}\right) g\big) = f(g)$ for all $x \in \mathbb{Q}_p$ and all $g$, and $f(\mathrm{diag}(a_0,a_1)\,g) = \chi_0(a_0)\chi_1(a_1)\,\sqrt{\|a_0\|/\|a_1\|}\; f(g)$ for all units $a_0,a_1$ and all $g$, the square root being the real one, cast to $\mathbb{C}$. Assume further that $f \neq 0$ and that $f(gk) = f(g)$ for all $g$ and all $k$ in [`AdelicDock.localLevelOne (𝓞 ℚ) ℚ p (p.asIdeal ^ b)`](def/AdelicDock_LocalEmbedding.html#L178), the subgroup of $\mathrm{GL}_2(\mathbb{Q}_p)$ consisting of those $k$ whose image under the embedding `localEmbed` into $\mathrm{GL}_2$ of the finite adeles (insert $k$ at $p$, the identity elsewhere) satisfies, together with its inverse, the level-one congruence condition `IsLevelOneMatrix` for the ideal $p^b$. Then for each $i \in \{0,1\}$ and every $u$ in `higherUnitsAt ℚ p b`, i.e. every unit $u$ of $\mathbb{Q}_p$ with $v(u) = 1$ and, unless $b = 0$, $v(u-1) \le \exp(-b)$, one has $\chi_i(u) = 1$.
--
--   This is the elementary inequality in Casselman's determination of the level of a principal series of $\mathrm{GL}_2(\mathbb{Q}_p)$: existence of a non-zero vector fixed by the level group attached to $p^b$ forces both inducing characters to be trivial on the $b$-th higher unit group, so their conductor exponents are at most $b$; no irreducibility is assumed and only this bound, not the exact level $a(\chi_0)+a(\chi_1)$, is asserted. The proof cites the Iwasawa decomposition [`LocalGL2.iwasawa_decomposition_diag`](thm.html#LocalGL2.iwasawa_decomposition_diag), and the result feeds into the local computation of Rankin–Selberg integrals for principal series vectors.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_forall_higherUnitsAt_eq_one_of_mem_principalSeries2_of_forall_mem_localLevelOne_pow.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_PrincipalSeries2
import Definitions.Def_LanglandsTunnell_TateLocalConstantsAt
import Definitions.Def_AdelicDock_LocalEmbedding

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField LanglandsTunnell.CubicInduction

theorem LanglandsTunnell.CubicInduction.forall_higherUnitsAt_eq_one_of_mem_principalSeries2_of_forall_mem_localLevelOne_pow
    (p : HeightOneSpectrum (𝓞 ℚ)) (χ : Fin 2 → ((p.adicCompletion ℚ)ˣ →* ℂˣ)) (b : ℕ)
    (f : GL (Fin 2) (p.adicCompletion ℚ) → ℂ) (hf : f ∈ principalSeries2 p χ) (hf0 : f ≠ 0)
    (hfK : ∀ k ∈ AdelicDock.localLevelOne (𝓞 ℚ) ℚ p (p.asIdeal ^ b),
      ∀ g : GL (Fin 2) (p.adicCompletion ℚ), f (g * k) = f g) :
    ∀ i : Fin 2, ∀ u ∈ LanglandsTunnell.TateLocal.higherUnitsAt ℚ p b, χ i u = 1 := by sorry
