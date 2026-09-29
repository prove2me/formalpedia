-- Prove2me | Theorems.Thm_LanglandsTunnell_Converse_sPart_shift
-- name    : LanglandsTunnell.Converse.sPart_shift
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:02.424499+00:00
-- url     : https://prove2.me/theorems/ecbd611a-1932-517d-a297-61e6cd356ecd
-- title:
--   Coefficient translation multiplies the S-part series by a monomial
-- statement:
--   Let $K$ be a number field, let $S$ be a finite set of height-one primes of the ring of integers $\mathcal{O}_K$, let $A\colon(S\to\mathbb{Z})\to\mathbb{C}$ be a family of complex numbers indexed by integer vectors on $S$, let $\mu\colon(\mathbb{A}_K)^\times\to\mathbb{C}^\times$ be a group homomorphism on the units of the adele ring of $\mathcal{O}_K$ in $K$, let $s\in\mathbb{C}$ and let $m\colon S\to\mathbb{Z}$. For $v\in S$ write $X_v=\mu(\varpi_v)\cdot N(v)^{1/2-s}$, where $\varpi_v$ is the idele `uniformizerIdele K v` — trivial in the archimedean component and, in the finite component, the unit which is $1$ at every prime other than $v$ and at $v$ is the image in $K_v$ of a chosen uniformizer of $v$ — the value $\mu(\varpi_v)$ being read as a complex number, $N(v)$ the absolute norm of the ideal $v$, and the power a complex `cpow`. The quantity `sPart K S A μ s` is the unconditional sum $\sum_{n\colon S\to\mathbb{Z}}A(n)\prod_{v\in S}X_v^{\,n_v}$ (so $0$ if the family is not summable). The assertion is $\bigl(\prod_{v\in S}X_v^{\,m_v}\bigr)\cdot$ `sPart K S A μ s` $=$ `sPart K S (fun n => A (n - m)) μ s`; no summability hypothesis is imposed.
--
--   An elementary bookkeeping identity for the $S$-part series attached to a family of coefficients: a monomial factor $\prod_{v\in S}\mu(\varpi_v)^{m_v}N(v)^{m_v(1/2-s)}$ occurring in a functional equation can be absorbed into a translation of the coefficient family. It is used in the converse-theorem part of the Langlands–Tunnell argument, by [`LanglandsTunnell.Converse.isNicePinned_sPart_shift`](thm.html#LanglandsTunnell.Converse.isNicePinned_sPart_shift) and by the two existence results [`LanglandsTunnell.Converse.exists_isJLNice_of_forall_isNicePinned`](thm.html#LanglandsTunnell.Converse.exists_isJLNice_of_forall_isNicePinned) and [`LanglandsTunnell.Converse.exists_jlData_isJLNice_of_forall_isNicePinned`](thm.html#LanglandsTunnell.Converse.exists_jlData_isJLNice_of_forall_isNicePinned).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_Converse_sPart_shift.lean

import Definitions.Def_LanglandsTunnell_ConverseData

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField IsDedekindDomain AutomorphicForm

theorem LanglandsTunnell.Converse.sPart_shift (K : Type) [Field K] [NumberField K]
    (S : Finset (HeightOneSpectrum (𝓞 K))) (A : (↥S → ℤ) → ℂ)
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (s : ℂ) (m : ↥S → ℤ) :
    (∏ v : ↥S,
        (((μ (uniformizerIdele K v.1) : ℂˣ) : ℂ) *
          ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ ((1 : ℂ) / 2 - s)) ^ (m v)) *
      sPart K S A μ s = sPart K S (fun n => A (n - m)) μ s := by sorry
