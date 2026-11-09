-- Prove2me | Theorems.Thm_GroupIsoPoly_theorem_1_1
-- name    : GroupIsoPoly.theorem_1_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T02:52:54.585143+00:00
-- url     : https://prove2.me/theorems/c438c837-a23e-4147-8879-bc8c8d96867a
-- title:
--   Theorem 1.1 — isomorphism of finite groups given by Cayley tables in time polynomial in the order
-- statement:
--   There are a deterministic algorithm and a constant $C$ with the following property. For every $N$, all finite groups $G,H$ of order $N$ and all labellings of their elements by $0,\dots,N-1$, the algorithm, given the two Cayley (multiplication) tables, halts within
--   $$
--   C\,(N+1)^C
--   $$
--   steps and outputs $1$ if $G\cong H$ and $0$ otherwise.
--
--   The previous best algorithm took time $N^{(1/4+o(1))\log N}$ (Rosenbaum 2013), barely below the $N^{\log N+O(1)}$ generator enumeration known since the 1970s. Group isomorphism was a recognised obstacle to putting graph isomorphism in P.
--
--   **Formalization Note** The machine is a Mathlib multi-stack Turing machine run through the published `HMBinPacking.OutputsWithin`; the input is the code `encPair` of the two tables, of length $\Theta(N^2\log N)$.
--
--   Differences from the source:
--
--   - reading: "an algorithm … in time polynomial in N" → one deterministic Mathlib TM2 machine `M` and one constant `C`, chosen before `N` and the groups, halting within `C·(N+1)^C` steps on every input pair; reason: the input has length Θ(N² log N), so poly(N) is poly(input length); Turing machines and RAMs simulate each other with polynomial overhead
--   - encoding: "given by their Cayley (multiplication) tables" → every labelling `G ≃ Fin N`, `H ≃ Fin N` of groups in `Type`, the tables coded row-major with `encodeNat` (`encPair`); reason: any standard table code differs polynomially; quantifying over every labelling is what "given by" means; every finite group is isomorphic to one in `Type`
--   - reading: "decides if G and H are isomorphic" → the single output bit `decide (Nonempty (G ≃* H))`; reason: the standard meaning of a decision algorithm
-- source:
--   Qiao, Zhang, Testing isomorphism of finite groups in time polynomial in the group order, preprint, Nov. 3, 2026 (held version sha256 eb9a3355…), Theorem 1.1, p.1 (PDF p.5)

import Mathlib
import Definitions.Def_HMBinPacking_OutputsWithin
import Definitions.Def_GroupIsoPoly_encPair

set_option autoImplicit false

namespace GroupIsoPoly

open Classical in
/-- **Theorem 1.1 (Group isomorphism in time polynomial in group order).**

Qiao, Zhang, *Testing isomorphism of finite groups in time polynomial in the group order*, preprint,
Nov. 3, 2026 (held version sha256 eb9a3355…), Theorem 1.1, p.1 (PDF p.5): "Let G and H be two finite
groups of order N, given by their Cayley (multiplication) tables. There is an algorithm that decides
if G and H are isomorphic in time polynomial in N."

There are one deterministic Turing machine `M` and one constant `C` such that for every `N`, all
groups `G, H` of order `N` and all labellings `G ≃ Fin N`, `H ≃ Fin N`, the machine `M`, started on
the code of the two Cayley tables, halts within `C·(N+1)^C` steps with output `1` if `G ≅ H` and `0`
otherwise.

**Formalization Note.** `M` is a Mathlib multi-stack Turing machine run through the published
`HMBinPacking.OutputsWithin`. The input is `encPair` of the two tables (length `Θ(N² log N)`), so
time polynomial in `N` is time polynomial in the input length. -/
theorem theorem_1_1 :
    ∃ M : Turing.TM2ComputableAux Bool Bool, ∃ C : ℕ,
      ∀ (N : ℕ) (G H : Type) [Group G] [Group H] (eG : G ≃ Fin N) (eH : H ≃ Fin N),
        HMBinPacking.OutputsWithin M (encPair N (cayley eG) (cayley eH))
          [decide (Nonempty (G ≃* H))] (C * (N + 1) ^ C) := by sorry

end GroupIsoPoly
