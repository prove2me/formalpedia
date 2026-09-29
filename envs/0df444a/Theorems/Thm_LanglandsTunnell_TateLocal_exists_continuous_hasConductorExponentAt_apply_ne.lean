-- Prove2me | Theorems.Thm_LanglandsTunnell_TateLocal_exists_continuous_hasConductorExponentAt_apply_ne
-- name    : LanglandsTunnell.TateLocal.exists_continuous_hasConductorExponentAt_apply_ne
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:09.28874+00:00
-- url     : https://prove2.me/theorems/b361c681-7424-5ea8-aaac-96d84496b9ec
-- title:
--   Characters of large exact conductor exponent avoiding a prescribed value
-- statement:
--   Let $K$ be a number field, $v$ a nonzero prime of its ring of integers $\mathcal{O}_K$ (a point of the height-one spectrum), and let $K_v$ denote the $v$-adic completion of $K$. Let $u_0 \in K_v^{\times}$ satisfy $\lvert u_0 \rvert_v = 1$ and $u_0 \neq 1$, let $z \in \mathbb{C}^{\times}$, and let $d$ be a natural number. Then there exist a natural number $c$ with $d \le c$ and $2 \le c$, and a group homomorphism $\chi : K_v^{\times} \to \mathbb{C}^{\times}$, such that: $\chi$ is continuous; $\chi$ is trivial on `uniformizerUnit K v`, the unit of $K_v$ obtained as the image of the chosen uniformizer `uniformizer v` of $\mathcal{O}_K$ at $v$; $\chi$ has exact conductor exponent $c$ in the sense of `HasConductorExponentAt`, i.e. $\chi(u) = 1$ for every unit $u$ with $\lvert u \rvert_v = 1$ and $\lvert u - 1 \rvert_v \le \exp(-c)$, while for each $m < c$ there is a unit $u$ with $\lvert u \rvert_v = 1$ and ($m = 0$ or $\lvert u - 1 \rvert_v \le \exp(-m)$) with $\chi(u) \neq 1$; and finally $\chi(u_0) \neq z$.
--
--   This is the local separation statement underlying the choice of auxiliary ramified characters in the Langlands–Tunnell argument: continuous characters of $K_v^{\times}$ that are trivial at the uniformizer and have arbitrarily large exact conductor exponent can be chosen so as to avoid any prescribed value at any prescribed unit other than $1$. It refines [`LanglandsTunnell.TateLocal.exists_continuous_hasConductorExponentAt`](thm.html#LanglandsTunnell.TateLocal.exists_continuous_hasConductorExponentAt), which supplies characters of any prescribed exponent $c \ge 2$, and is used in the construction of pinned Rankin–Selberg data.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_TateLocal_exists_continuous_hasConductorExponentAt_apply_ne.lean

import Definitions.Def_LanglandsTunnell_TateLocalConstantsAt

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.AdelicLevel IsDedekindDomain

theorem LanglandsTunnell.TateLocal.exists_continuous_hasConductorExponentAt_apply_ne
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (u₀ : (v.adicCompletion K)ˣ) (hu : Valued.v (u₀ : v.adicCompletion K) = 1) (hu₀ : u₀ ≠ 1)
    (z : ℂˣ) (d : ℕ) :
    ∃ c : ℕ, d ≤ c ∧ 2 ≤ c ∧ ∃ χ : (v.adicCompletion K)ˣ →* ℂˣ,
      Continuous χ ∧ χ (uniformizerUnit K v) = 1 ∧ HasConductorExponentAt K v χ c ∧ χ u₀ ≠ z := by sorry
