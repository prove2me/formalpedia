-- Prove2me | Theorems.Thm_ITPIRPreproc_MatchVec_polynomial_indexed_computability
-- name    : ITPIRPreproc.MatchVec.polynomial_indexed_computability
-- status  : Open
-- author  : @Jesko
-- created : 2026-11-13T17:21:59.14648+00:00
-- url     : https://prove2.me/theorems/e530af3b-90e8-47f0-a5ab-d7034937df91
-- title:
--   Appendix A — uniform RAM implementation of the indexed polynomial construction
-- statement:
--   Use Appendix A's least word length $\ell(h)$, prime-power exponents $a(h),b(h)$, degree cutoff $k(h)$, and explicit binomial-inversion coefficients. There exist injective row enumerations of $2^h$ distinct words in $[\ell(h)]^{\ell(h)}$, bijective coordinate enumerations by $[d(h)]$ of all $(I,\alpha)$ with $|I|\le k(h)$, absolute constants $C_0,c_0$, and two deterministic word-RAM programs, uniform in $h$.
--
--   For every $h\ge3$, the first program receives $(h,r)$ and outputs the two polynomial matching vectors of row $r$ in the selected coordinate order within work $C_0d(h)h^{c_0}$. The second receives $h$ and outputs the full table in row order within work $C_0 2^h d(h)h^{c_0}$ and working storage $C_0 2^h d(h)$. Every coordinate is encoded in the existing three-bit encoding of $\mathbb Z_6$.
--
--   This is the implementation part of Appendix A's final paragraph, isolated from its algebraic correctness and dimension analysis. The intended row enumeration is the first $2^h$ lexicographic words. The statement permits any injective row enumeration and bijective coordinate enumeration realized by the programs. It requires actual halting, outputs, and resource bounds in the mission's word-RAM model; mathematical computability alone does not suffice.
-- source:
--   Jesko Dujmovic, Zhengnan Lai, Daniel Wichs, Nearly Optimal Information-Theoretic PIR with Client Preprocessing, STOC 2027 submission #572, Appendix A, printed pp.36-37 (PDF pp.38-39), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/572.pdf

import Definitions.Def_ITPIRPreproc_MatchVec_PolynomialParameters
open ITPIRPreproc.MatchVec ITPIRPreproc.MatchVec.PolynomialConstruction

theorem ITPIRPreproc.MatchVec.polynomial_indexed_computability :
    ∃ (dim : ℕ → ℕ)
      (rows : ∀ h : ℕ, Fin (2^h) ↪ (Fin (wordLength h) → Fin (wordLength h)))
      (coords : ∀ h : ℕ, Fin (dim h) ≃
        Coordinate (wordLength h) (degree (exponent2 h) (exponent3 h)))
      (C₀ : ℝ) (c₀ : ℕ) (vecProg tableProg : WordRAM.Program),
      MVComputable dim
        (fun h r j => leftVector (coefficient (wordLength h) (exponent2 h) (exponent3 h))
          (rows h r) (coords h j))
        (fun h r j => rightVector (rows h r) (coords h j))
        C₀ c₀ vecProg tableProg := by sorry
