-- Prove2me | Theorems.Thm_LanglandsTunnell_Converse_isNicePinned_sPart_shift
-- name    : LanglandsTunnell.Converse.isNicePinned_sPart_shift
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:02.424499+00:00
-- url     : https://prove2.me/theorems/ec4ee9e0-9bc5-58a7-81c5-179ed72d5444
-- title:
--   Index shift of S-part coefficients preserves pinned niceness
-- statement:
--   Let $K$ be a number field, $\iota$ a type and $D$ an $L$-datum indexed by $\iota$ (Euler polynomials `euler`, dual polynomials `dual`, norms, archimedean shift multisets, abscissa, centre, degree) whose centre equals $1/2$; let $S$ be a finite set of height-one primes of $\mathcal{O}_K$, let $A, A^\vee : \mathbb{Z}^S \to \mathbb{C}$, let $\mu$ be a monoid homomorphism from the idele units of $K$ to $\mathbb{C}^\times$, let $\varepsilon \in \mathbb{C}$, $N \in \mathbb{R}$ and $k \in \mathbb{Z}^S$. Here $\mathrm{sPart}(K,S,A,\mu)(s) = \sum_{n \in \mathbb{Z}^S} A(n) \prod_{v \in S} \bigl(\mu(\varpi_v)\, q_v^{1/2-s}\bigr)^{n_v}$, with $\varpi_v$ the idele `uniformizerIdele` at $v$ and $q_v$ the absolute norm of $v$, and $\mathrm{sPartDual}$ is the same expression with $\mu(\varpi_v)^{-1}$ in place of $\mu(\varpi_v)$. Assume `IsNicePinned` holds for $D$, the pair $(\mathrm{sPart}(K,S,A,\mu), \mathrm{sPartDual}(K,S,A^\vee,\mu))$, $\varepsilon$ and $N$: the predicates `D.WellFormed` and `D.Converges` hold, $N > 0$, and there exist entire $\Lambda, \Lambda^\vee$, each `BoundedOnStrips`, agreeing for $\operatorname{Re} s$ beyond `D.abscissa` with the respective $S$-part series times `archFactor` and `LFun`, resp. `archFactorDual` and `LFunDual`, and satisfying $\Lambda(s) = \varepsilon N^{\,c-s}\Lambda^\vee(2c-s)$ with $c$ the centre. Then the same conclusion holds for the shifted families $n \mapsto A(n-k)$ and $n \mapsto A^\vee(n+k)$, with the same $\varepsilon$ and $N$.
--
--   This is the bookkeeping step in the converse theorem by which a monomial factor $\prod_{v \in S}(\mu(\varpi_v) q_v^{1/2-s})^{k_v}$ occurring in a functional equation is absorbed into the coefficient families by translating their indices, the dual family being translated in the opposite direction. It is used in the construction of Jacquet–Langlands data satisfying the niceness conditions, in [`LanglandsTunnell.Converse.exists_jlData_isJLNice_of_forall_isNicePinned`](thm.html#LanglandsTunnell.Converse.exists_jlData_isJLNice_of_forall_isNicePinned), and rests on the identity `sPart_shift` together with `sPartDual_eq_sPart_inv`.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_Converse_isNicePinned_sPart_shift.lean

import Definitions.Def_LanglandsTunnell_ConverseData

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField

theorem LanglandsTunnell.Converse.isNicePinned_sPart_shift (K : Type) [Field K] [NumberField K]
    {ι : Type} (D : LanglandsTunnell.LDatum ι) (hc : D.center = 1 / 2)
    (S : Finset (HeightOneSpectrum (𝓞 K))) (A Ad : (↥S → ℤ) → ℂ)
    (μ : (AdeleRing (𝓞 K) K)ˣ →* ℂˣ) (ε : ℂ) (N : ℝ) (k : ↥S → ℤ)
    (h : IsNicePinned D (sPart K S A μ) (sPartDual K S Ad μ) ε N) :
    IsNicePinned D (sPart K S (fun n => A (n - k)) μ) (sPartDual K S (fun n => Ad (n + k)) μ) ε N := by sorry
