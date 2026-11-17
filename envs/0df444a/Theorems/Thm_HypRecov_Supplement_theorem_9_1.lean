-- Prove2me | Theorems.Thm_HypRecov_Supplement_theorem_9_1
-- name    : HypRecov.Supplement.theorem_9_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-17T03:28:16.395847+00:00
-- url     : https://prove2.me/theorems/d531297f-cdc2-441f-a314-e23ca0dcb185
-- title:
--   Theorem 9.1 — deterministic sparse signed-integer recovery
-- statement:
--   Fix $n\ge r\ge1$ and $K,W\ge1$, and put
--   $$q=\min\{r,1+\lfloor\log_2K\rfloor\},\quad L=\lceil\log_2(2W+1)\rceil,$$
--   $$a=\max_{0\le h\le q}\nu_2\binom{r-h}{q-h}.$$
--   There is one uniform deterministic additive sketch of an integer $q$-fragment stream whose terminal vector is $W_{q,r}z$. Whenever $\|z\|_0\le K$ and $\|z\|_\infty\le W$, it returns every nonzero $r$-set coordinate and its exact signed value.
--
--   State, deterministic description, output and decoding workspace use $O(Kr\log(n+1)(a+L))$ bits; initialization, unit updates and decoding are polynomial in $n,r,K,\log W$, and a general increment adds polynomial dependence on its bit length. Since $a\le\lfloor\log_2r\rfloor$, the stated simplified space bound follows. For $n\ge2r$, $q$ is the least possible order even for zero-one $K$-sparse vectors.
--
--   Differences from the source:
--   - encoding: an integer vector indexed by $r$-subsets → a total function on vertex subsets required to vanish off the $r$-uniform slice; reason: the two representations have exactly the same coordinates
--   - encoding: deterministic additive sketch and big-O/polynomial bounds → uniform TM2 machines, binary increment/output encodings, explicit absolute constants and all-stack bounds; reason: this makes the paper's resource claims and per-unit/general-increment distinction kernel-auditable without changing an instance
-- source:
--   Zhang, Chen, Shen, Hypergraph Recovery from Anonymous Projection Streams, STOC 2027 submission (manuscript sha256 719dcfff4dc2eba2d8c5a3c51679a08cfb11f076546dea963c6376a2b9da2c82), Theorem 9.1, p.22 (PDF p.23)

import Mathlib
import Definitions.Def_HypRecov_Supplement_QuerySketchGuarantee

set_option autoImplicit false

namespace HypRecov.Supplement

/-- **Theorem 9.1 (Sparse integer recovery from anonymous projections).** Zhang, Chen, Shen,
*Hypergraph Recovery from Anonymous Projection Streams*, STOC 2027 submission (manuscript sha256
719dcfff…), Theorem 9.1, p.22 (PDF p.23).

At order `q=min{r,1+floor(log₂ K)}`, one uniform deterministic additive sketch exactly recovers
every signed integer vector on `r`-sets with support at most `K` and coefficient magnitude at most
`W`.  With `L=ceil(log₂(2W+1))` and the displayed 2-adic precision `a`, all state, deterministic
description, output and workspace use `O(K r log(n+1) (a+L))` bits; initialization, unit updates and
decoding are uniformly polynomial, and a general increment is polynomial also in its bit length.
The clause `a ≤ floor(log₂ r)` gives the theorem's simplified space bound.  For `n ≥ 2r`, `q` is
the least possible order even on zero-one vectors.

**Formalization Note.** The latent vector is not restricted to a hypergraph: it is an arbitrary
integer-valued function, zero off the `r`-uniform slice.  `VectorSketchGuarantee` includes state
subtraction, so it also covers reconciliation of two dense inputs. -/
theorem theorem_9_1 :
    ∃ (A : HypRecov.LinearSketch) (C c : ℕ),
      ∀ (n r K W : ℕ), r ≤ n → 1 ≤ r → 1 ≤ K → 1 ≤ W →
        let q := sparseOrder r K
        let L := Nat.clog 2 (2 * W + 1)
        let a := projectionPrecision r q
        VectorSketchGuarantee A C c n r K W q a L ∧
          a ≤ Nat.log 2 r ∧
          (2 * r ≤ n →
            IsLeast {q' : ℕ | 1 ≤ q' ∧ q' ≤ r ∧ DeterminesSparseInteger n r K q'} q)
    := by sorry

end HypRecov.Supplement
