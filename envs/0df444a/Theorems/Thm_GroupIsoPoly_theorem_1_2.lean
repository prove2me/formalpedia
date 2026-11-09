-- Prove2me | Theorems.Thm_GroupIsoPoly_theorem_1_2
-- name    : GroupIsoPoly.theorem_1_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T02:54:53.007625+00:00
-- url     : https://prove2.me/theorems/e255a355-aa2d-45ec-896a-614ef6d76d44
-- title:
--   Theorem 1.2 — 3-tensor isomorphism over $\mathbb F_q$ in time $q^{O(\ell+m+n)}$
-- statement:
--   There are a deterministic algorithm and a constant $C$ such that for every finite field $\mathbb F_q$ (given by a presentation), all $\ell,m,n$ and all $\ell\times m\times n$ 3-way arrays $A,B$ over $\mathbb F_q$, the algorithm decides whether $A$ and $B$ are isomorphic as 3-tensors (Definition 1) within
--   $$
--   C\cdot q^{\,C\max(\ell+m+n,\,1)}
--   $$
--   steps.
--
--   The previous best bound for $n\times n\times n$ tensors was $q^{\tilde O(n^{1.5})}$. By [GQ23b], this running time is equivalent to polynomial-time isomorphism testing of $p$-groups of class 2 and exponent $p$, the case usually regarded as the bottleneck of group isomorphism.
--
--   **Formalization Note** The instance code is `enc3TI` (dimensions, field, entries). There is no $\mathrm{poly}(\mathrm{InSize})$ factor: the input length is below the bound.
--
--   Differences from the source:
--
--   - reading: time q^O(ℓ+m+n) → C · q^(C·max(ℓ+m+n, 1)) steps of one machine, C chosen before the field and the dimensions; reason: for ℓ+m+n ≥ 1 this is the printed bound (the input length O(ℓmn log q + e log p) is below it); when all dimensions are 0 the printed bound O(1) does not cover reading the field description, which every machine must read
--   - encoding: arrays / tensors over F_q → a presented field `P : FieldPres` (q = p^e) in the input, entries in power-basis coordinates; reason: an algorithm over every F_q needs the field in its input; every finite field has a presentation
-- source:
--   Qiao, Zhang, Testing isomorphism of finite groups in time polynomial in the group order, preprint, Nov. 3, 2026 (held version sha256 eb9a3355…), Theorem 1.2, p.2 (PDF p.6); Definition 1, p.1 (PDF p.5)

import Mathlib
import Definitions.Def_HMBinPacking_OutputsWithin
import Definitions.Def_GroupIsoPoly_TensorIso
import Definitions.Def_GroupIsoPoly_enc3TI

set_option autoImplicit false

namespace GroupIsoPoly

open AvgCaseTI (FieldPres)

open Classical in
/-- **Theorem 1.2 (Tensor isomorphism in singly exponential time).**

Qiao, Zhang, *Testing isomorphism of finite groups in time polynomial in the group order*, preprint,
Nov. 3, 2026 (held version sha256 eb9a3355…), Theorem 1.2, p.2 (PDF p.6): "Let A, B be two ℓ × m × n
3-way arrays over Fq. There is an algorithm that decides if A and B are isomorphic as tensors in time
q^O(ℓ+m+n)."

There are one deterministic machine `M` and one constant `C` such that for every presented finite
field `F_q`, all `ℓ, m, n` and all `ℓ × m × n` arrays `A, B` over `F_q`, `M` on the code of
`(ℓ, m, n, F, A, B)` halts within `C · q^(C · max(ℓ+m+n, 1))` steps with output `1` if `A` and `B` are
isomorphic as 3-tensors (Definition 1) and `0` otherwise.

**Formalization Note.** `max(ℓ+m+n, 1)` equals `ℓ+m+n` unless all three dimensions are `0`, where it
lets the machine read the field. No `poly(InSize)` factor: the input length is below the bound. -/
theorem theorem_1_2 :
    ∃ M : Turing.TM2ComputableAux Bool Bool, ∃ C : ℕ,
      ∀ (P : FieldPres) (l m n : ℕ) (A B : Array3 P.F l m n),
        HMBinPacking.OutputsWithin M (enc3TI P l m n A B) [decide (TensorIso A B)]
          (C * P.q ^ (C * max (l + m + n) 1)) := by sorry

end GroupIsoPoly
