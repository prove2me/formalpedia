-- Prove2me | Theorems.Thm_InfoLossLAR_WorstCase_lemma_6_5
-- name    : InfoLossLAR.WorstCase.lemma_6_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T02:03:57.773585+00:00
-- url     : https://prove2.me/theorems/74db05b6-6353-44e5-9d8b-35fdb7a117fa
-- title:
--   Lemma 6.5 — the canonical endpoint pullback $c_T:H_0\to\mathcal F_{T,0}$ is a bijection
-- statement:
--   Let $q$ be an odd prime, $d\ge q$, $T$ the matrix of Definition 6.3, $H_0=\{\bar w\in\mathbb F_q^d:\mathbf 1^\top\bar w=0\}$ and $\mathcal F_{T,0}$ the zero fiber of $f_T(x)=\sum_j\lfloor (T[x]_q)_j/q\rfloor\bmod q$. The map
--   $$c_T:H_0\to\mathcal F_{T,0},\qquad c_T(\bar w)=T^{-1}[\bar w]_q\bmod q,$$
--   is a bijection, with inverse $c_T^{-1}(x)=T[x]_q\bmod q$ for $x\in\mathcal F_{T,0}$.
--
--   Differences from the source:
--   - encoding: "with inverse $c_T^{-1}(x)=T[x]_q\bmod q$" → for every $x\in\mathcal F_{T,0}$, $T[x]_q\bmod q\in H_0$ and $c_T(T[x]_q\bmod q)=x$; reason: given the bijection, this identifies the inverse
--   - encoding: $T^{-1}[\bar w]_q$ integral → each entry read through its numerator; reason: the entries are integers on $H_0$
-- source:
--   Chen Qian, Information Loss Is All You Need: TC⁰ Pseudorandomness from Worst-Case Lattices, arXiv:2611.05136 (held version, sha256 2ebdfbf3…), p. 28, Lemma 6.5

import Mathlib
import Definitions.Def_InfoLossLAR_WorstCase_Rounding
import Definitions.Def_InfoLossLAR_WorstCase_FixedT

set_option autoImplicit false

namespace InfoLossLAR.WorstCase

/-- Lemma 6.5 (Canonical parametrization of the zero fiber), p. 28: for `q` an odd prime,
`d ≥ q` and `T` of Definition 6.3, `c_T(w̄) = T^{-1}[w̄]_q mod q` is a bijection from `H_0` onto
`F_{T,0}`, with inverse `x ↦ T[x]_q mod q` on `F_{T,0}`. -/
theorem lemma_6_5 (q d : ℕ) [Fact q.Prime] (hq2 : q ≠ 2) (hdq : q ≤ d) :
    Set.BijOn (cT q d) (H0 q d) (zeroFiber63 q d) ∧
    ∀ x ∈ zeroFiber63 q d,
      modq q ((TDef63 q d).mulVec (lift x)) ∈ H0 q d ∧
      cT q d (modq q ((TDef63 q d).mulVec (lift x))) = x := by sorry

end InfoLossLAR.WorstCase
