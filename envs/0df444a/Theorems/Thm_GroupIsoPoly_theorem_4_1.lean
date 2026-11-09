-- Prove2me | Theorems.Thm_GroupIsoPoly_theorem_4_1
-- name    : GroupIsoPoly.theorem_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T02:54:35.249581+00:00
-- url     : https://prove2.me/theorems/3803d189-f794-4d2d-8ba1-f402868311c9
-- title:
--   Theorem 4.1 — matrix tuple congruence over $\mathbb F_{2^f}$ in time $2^{O(fn)}\cdot\mathrm{poly}(n,m)$
-- statement:
--   There are a deterministic algorithm and a constant $C$ such that for every finite field $\mathbb F_{2^e}$ of characteristic 2 (given by a presentation), all $n,m$ and all tuples $A=(A_1,\dots,A_m)$, $B=(B_1,\dots,B_m)\in M(n,2^e)^m$, the algorithm decides whether $A$ and $B$ are congruent — whether some $L\in\mathrm{GL}(n,2^e)$ has $A_i=LB_iL^t$ for all $i$ — within
--   $$
--   C\cdot2^{\,C\,e\,\max(n,1)}\cdot(n+m+2)^C
--   $$
--   steps.
--
--   In odd characteristic matrix tuple congruence is solved by $*$-algebra methods; characteristic 2 is the obstacle, and this theorem is the step that lets the 3-tensor isomorphism algorithm handle all finite fields. With $e=1$ (and Corollary 4.2) it is Theorem 1.3.
--
--   **Formalization Note** The instance code lists $n$, $m$, the field and the entries (`encMTC`); the machine is run through the published `HMBinPacking.OutputsWithin`.
--
--   Differences from the source:
--
--   - reading: 2^O(fn) · poly(n, m)-time → C · 2^(C·e·max(n,1)) · (n+m+2)^C steps of one machine, C chosen before the field and the dimensions; reason: for n ≥ 1 this is the printed bound; at n = 0 the printed bound poly(m) does not cover reading the field description (Θ(e) bits), which every machine must read, so the corner n = 0 is read with exponent e
--   - encoding: matrices over F_{2^f} → a presented field `P : FieldPres` with `P.p = 2`, exponent e = deg of the defining polynomial, in the input with entries in power-basis coordinates; reason: an algorithm over every F_{2^f} needs the field in its input; every finite field has a presentation; the paper's letter f is renamed e because `P.f` is the polynomial
-- source:
--   Qiao, Zhang, Testing isomorphism of finite groups in time polynomial in the group order, preprint, Nov. 3, 2026 (held version sha256 eb9a3355…), Theorem 4.1, p.27 (PDF p.31); Definition 10, p.27

import Mathlib
import Definitions.Def_HMBinPacking_OutputsWithin
import Definitions.Def_GroupIsoPoly_Congruent
import Definitions.Def_GroupIsoPoly_encMTC

set_option autoImplicit false

namespace GroupIsoPoly

open AvgCaseTI (FieldPres)

open Classical in
/-- **Theorem 4.1 (Matrix tuple congruence algorithm over `F_{2^f}`).**

Qiao, Zhang, *Testing isomorphism of finite groups in time polynomial in the group order*, preprint,
Nov. 3, 2026 (held version sha256 eb9a3355…), Theorem 4.1, p.27 (PDF p.31): "Let A = (A1, . . . , Am),
B = (B1, . . . , Bm) ∈ M(n, 2^f)^m be two tuples of matrices. There is a 2^O(fn) · poly(n, m)-time
algorithm that decides whether the two tuples are congruent."

There are one deterministic machine `M` and one constant `C` such that for every presented field
`F_{2^e}` (characteristic 2, `e = deg f`), all `n, m` and all `A, B ∈ M(n, 2^e)^m`, `M` on the code of
`(n, m, F, A, B)` halts within `C · 2^(C·e·max(n,1)) · (n + m + 2)^C` steps with output `1` if `A` and
`B` are congruent and `0` otherwise.

**Formalization Note.** The paper's exponent `f` is `e = P.f.natDegree` here (`P.f` is the defining
polynomial). `max(n, 1)` equals `n` for `n ≥ 1`; at `n = 0` it lets the machine read the field. -/
theorem theorem_4_1 :
    ∃ M : Turing.TM2ComputableAux Bool Bool, ∃ C : ℕ,
      ∀ P : FieldPres, P.p = 2 →
      ∀ (n m : ℕ) (A B : Fin m → Matrix (Fin n) (Fin n) P.F),
        HMBinPacking.OutputsWithin M (encMTC P n m A B) [decide (Congruent A B)]
          (C * 2 ^ (C * P.f.natDegree * max n 1) * (n + m + 2) ^ C) := by sorry

end GroupIsoPoly
