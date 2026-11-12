-- Prove2me | Theorems.Thm_ITPIRPreproc_MatchVec_matching_vectors_eq7
-- name    : ITPIRPreproc.MatchVec.matching_vectors_eq7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T07:10:00.381088+00:00
-- url     : https://prove2.me/theorems/f1749c1b-abe2-4835-8fe8-d1177b5077c0
-- title:
--   §5.2, Eq. (7) — computable matching vectors mod 6 with distinct mod-2 reductions in dimension $2^{O(\sqrt{h\log h})}$
-- statement:
--   For $h\ge3$ let $m=2^h$. There are a dimension function $d=\dim(h)$ and, for every $h\ge3$, pairs $u_a,v_a\in\mathbb Z_6^{d}$, $a\in[m]$, such that
--
--   1. the family satisfies (7):
--   $$\forall a:\ \langle u_a,v_a\rangle_6=1,\qquad \forall a\ne a':\ \langle u_{a'},v_a\rangle_2=0\ \text{ or }\ \langle u_{a'},v_a\rangle_3=0,$$
--   and the vectors $v_a\bmod 2$ are pairwise distinct;
--   2. $d\le 2^{C\sqrt{h\log h}}$ for an absolute constant $C$;
--   3. the family is computable: one deterministic word-RAM program outputs $u_a,v_a$ from $(h,a)$ within work $C_0\,d\,h^{c_0}$, and another outputs the whole table from $h$ within work $C_0\,m\,d\,h^{c_0}$ and storage $C_0\,m\,d$, for absolute constants $C_0,c_0$.
--
--   This is the matching-vector family that the primitives of §5.3 and §6.2 are built on; the computability clause is what the running times of Lemma 6.2, and through it the work bounds of Theorem 6.1, rely on. The paper obtains it from the diagonal-one matching vectors of Alon, Beimel and Lasri, based on Grolmusz's construction, and gives an indexed version in Appendix A.
--
--   **Formalization Note** Vectors are encoded with $3$ bits per coordinate. Appendix A's choice of $q_p$ as the least power of $p$ exceeding $\ell$ must read "exceeding $\sqrt\ell$" for its dimension bound; this statement is the §5.2 claim and does not depend on that choice.
--
--   Differences from the source:
--   - reading: d = 2^{O(√(h log h))} → one absolute constant C with dim h ≤ 2^{C√(h ln h)} for every h ≥ 3; reason: an O(·) in an exponent is one constant chosen before h (paper.md Reading 1); the log base is absorbed by C
--   - reading: construction of such a family in md poly(h) time and O(md) space, with each vector computable from its row index in d poly(h) time → deterministic word-RAM programs with work ≤ C₀·d·h^{c₀} per pair, ≤ C₀·m·d·h^{c₀} for the table, and table storage ≤ C₀·m·d, for absolute C₀, c₀; reason: time and space in the RAM model of §3 (paper.md Reading 2); poly(h) is h^{c₀} with constants chosen before h
--   - generalization: for each h, a family and a construction → one dimension function, one family indexed by h and one pair of programs for all h ≥ 3; reason: Appendix A makes the vectors public functions of n and a; a uniform construction specializes to every fixed h
--   - encoding: u_a, v_a ∈ Z_6^d, a ∈ [m] → Fin m → Fin d → ZMod 6, coordinates coded in 3 bits; reason: Lean convention; same objects
-- source:
--   Jesko Dujmovic, Zhengnan Lai, Daniel Wichs, Nearly Optimal Information-Theoretic PIR with Client Preprocessing, STOC 2027 submission #572 (October 2026), §5.2, printed p.17 (PDF p.19), Eq. (7) and the paragraph after it; Appendix A, printed pp.35–37 (PDF pp.37–39)

import Mathlib
import Definitions.Def_ITPIRPreproc_MatchVec_MatchingVectors

namespace ITPIRPreproc.MatchVec

/-- §5.2, Eq. (7), printed p.17 (PDF p.19); construction in Appendix A, printed pp.35–37.
For `h ≥ 3` (`m = 2^h ≥ 8`) there are `m` pairs `u_a, v_a ∈ Z_6^d` satisfying (7) with the
`v_a mod 2` pairwise distinct, of dimension `d ≤ 2^{C√(h log h)}` for an absolute `C`, computable
(one pair from its index in `d·poly(h)` work, the whole table in `m·d·poly(h)` work and `O(md)`
working bits) by one pair of word-RAM programs for all `h`. -/
theorem matching_vectors_eq7 :
    ∃ (dim : ℕ → ℕ) (u v : ∀ h : ℕ, Fin (2 ^ h) → Fin (dim h) → ZMod 6)
      (C C₀ : ℝ) (c₀ : ℕ) (vecProg tableProg : WordRAM.Program),
      (∀ h : ℕ, 3 ≤ h →
        IsMVFamily (2 ^ h) (dim h) (u h) (v h) ∧
        (dim h : ℝ) ≤ 2 ^ (C * Real.sqrt (h * Real.log h))) ∧
      MVComputable dim u v C₀ c₀ vecProg tableProg := by sorry

end ITPIRPreproc.MatchVec
