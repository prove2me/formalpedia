-- Prove2me | Theorems.Thm_LanglandsTunnell_Converse_exists_even_isAdmissibleTwist_hasConductorExponentAt_of_three_le
-- name    : LanglandsTunnell.Converse.exists_even_isAdmissibleTwist_hasConductorExponentAt_of_three_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:02.424499+00:00
-- url     : https://prove2.me/theorems/8c49c1c0-e3a5-5cb8-8695-22c9d3fecb2c
-- title:
--   Even idele class characters of ℚ with prescribed conductors
-- statement:
--   Let $S$ be a finite set of nonzero primes of $\mathbb{Z} = \mathcal{O}_{\mathbb{Q}}$ and let $c$ assign a natural number to every such prime, with $c(v) \ge 3$ for all $v \in S$. Then there is a group homomorphism $\chi$ from the units of the adele ring of $\mathbb{Q}$ to $\mathbb{C}^{\times}$ with the following four properties. First, `IsAdmissibleTwist`: $\chi$ is trivial on the image of $\mathbb{Q}^{\times}$ under the diagonal embedding, $\chi$ is continuous, and $|\chi(x)| = 1$ for every idele unit $x$. Second, for each $v \in S$ the local component $\chi_v$, obtained by composing $\chi$ with the inclusion of $(\mathbb{Q}_v)^{\times}$ into the finite ideles (component $1$ away from $v$, and $1$ at the infinite place), has conductor exponent exactly $c(v)$ in the sense of `HasConductorExponentAt`: $\chi_v$ is trivial on all local units $u$ with $|u - 1| \le |\pi_v|^{c(v)}$, while for every $m < c(v)$ some local unit $u$ with $|u-1| \le |\pi_v|^{m}$ (no condition when $m = 0$) has $\chi_v(u) \ne 1$. Third, for every prime $v \notin S$, $\chi_v$ is trivial on the units of the valuation ring of $\mathbb{Q}_v$. Fourth, at each real infinite place $w$ of $\mathbb{Q}$ the archimedean component satisfies `IsArchCompAt ℚ χ w 0 0`, i.e. it equals $\|x\|^{0}\,(x/\|x\|)^{0}$, so $\chi$ is even at $w$.
--
--   This is the existence statement for auxiliary twisting characters used in the converse-theorem part of the Langlands–Tunnell argument: an even Hecke character of $\mathbb{Q}$ of finite order with prescribed local conductor exponents at a given finite set of primes and unramified elsewhere. It is invoked by the cubic induction lemmas, where the twist must raise the conductor at chosen primes (whence the requirement $c(v) \ge 3$) without altering the behaviour at the real place; the proof cites the construction of idele class characters from primitive Dirichlet characters, their local conductor exponents, and stability of conductor exponents under multiplication by an unramified character.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_Converse_exists_even_isAdmissibleTwist_hasConductorExponentAt_of_three_le.lean

import Definitions.Def_LanglandsTunnell_ConverseData

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField NumberField.TateGlobal LanglandsTunnell.Converse

theorem LanglandsTunnell.Converse.exists_even_isAdmissibleTwist_hasConductorExponentAt_of_three_le
    (S : Finset (HeightOneSpectrum (𝓞 ℚ))) (c : HeightOneSpectrum (𝓞 ℚ) → ℕ) (hc : ∀ v ∈ S, 3 ≤ c v) :
    ∃ χ : (AdeleRing (𝓞 ℚ) ℚ)ˣ →* ℂˣ, IsAdmissibleTwist ℚ χ ∧
      (∀ v ∈ S, LanglandsTunnell.TateLocal.HasConductorExponentAt ℚ v (localChar χ v) (c v)) ∧
      (∀ v : HeightOneSpectrum (𝓞 ℚ), v ∉ S → IsUnramifiedCharAt χ v) ∧
      ∀ w : InfinitePlace ℚ, w.IsReal → IsArchCompAt ℚ χ w 0 0 := by sorry
