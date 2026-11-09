-- Prove2me | Theorems.Thm_GroupIsoPoly_theorem_9_1
-- name    : GroupIsoPoly.theorem_9_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T02:54:22.526723+00:00
-- url     : https://prove2.me/theorems/c01a0f12-e027-4884-9f43-39692c2e4af4
-- title:
--   Theorem 9.1 — the isomorphism coset $\mathrm{Iso}(G,H)$ of groups given by Cayley tables in time $\mathrm{poly}(N)$
-- statement:
--   There are a deterministic algorithm and a constant $C$ with the following property. For every $N$ and all groups $G,H$ of order $N$, given by Cayley tables under arbitrary labellings, the algorithm halts within $C(N+1)^C$ steps and outputs the isomorphism coset: emptiness if $G\not\cong H$, and otherwise an isomorphism $\varphi:G\to H$ together with automorphisms of $G$ that generate $\mathrm{Aut}(G)$, so that
--   $$
--   \mathrm{Iso}(G,H)=\varphi\cdot\mathrm{Aut}(G).
--   $$
--
--   This is the paper's form of the main result; Theorem 1.1 is its decision version. It also gives generators of $\mathrm{Aut}(G)$ in polynomial time for every group given by its table.
--
--   **Formalization Note** Maps are output as tables of labels (`encIsoAnswer`); the machine is run through the published `HMBinPacking.OutputsWithin`.
--
--   Differences from the source:
--
--   - reading: "an algorithm … in time polynomial in N" → one deterministic Mathlib TM2 machine `M` and one constant `C`, chosen before `N` and the groups, halting within `C·(N+1)^C` steps on every input pair; reason: the input has length Θ(N² log N), so poly(N) is poly(input length); Turing machines and RAMs simulate each other with polynomial overhead
--   - encoding: "given by their Cayley (multiplication) tables" → every labelling `G ≃ Fin N`, `H ≃ Fin N` of groups in `Type`, the tables coded row-major with `encodeNat` (`encPair`); reason: any standard table code differs polynomially; quantifying over every labelling is what "given by" means; every finite group is isomorphic to one in `Type`
--   - reading: "computes the coset Iso(G, H)" → an output coding emptiness iff `G ≇ H`, else an isomorphism `φ` and a list of automorphisms generating all of `Aut(G)` (`CosetCorrect` with `Trans = Iso(G,H)`, `Stab = Aut(G)`); reason: Iso(G, H) = φ·Aut(G); §9.6, p.119: "These lifts and kernel generators generate Aut(G)"
--   - reading: "Let G and H be two finite groups of order N" → groups given by their Cayley tables (`encPair`), as in Theorem 1.1; reason: p.92: "including computation of the isomorphism coset for groups given by their multiplication tables"
--   - reading: output elements with straight-line programs in the input generators (§3.5, p.19) → output elements written as themselves (label tables, matrix entries, permutation images); reason: for permutation and matrix groups each form is computable from the other in polynomial time (constructive membership, §3.5 (i), p.20); the coset is the same
-- source:
--   Qiao, Zhang, Testing isomorphism of finite groups in time polynomial in the group order, preprint, Nov. 3, 2026 (held version sha256 eb9a3355…), Theorem 9.1, p.92 (PDF p.96); §9.6, pp.118–119 (PDF pp.122–123)

import Mathlib
import Definitions.Def_HMBinPacking_OutputsWithin
import Definitions.Def_GroupIsoPoly_encPair
import Definitions.Def_GroupIsoPoly_CosetCorrect
import Definitions.Def_GroupIsoPoly_encIsoAnswer

set_option autoImplicit false

namespace GroupIsoPoly

/-- **Theorem 9.1 (Group isomorphism in time polynomial in group order) — the isomorphism coset.**

Qiao, Zhang, *Testing isomorphism of finite groups in time polynomial in the group order*, preprint,
Nov. 3, 2026 (held version sha256 eb9a3355…), Theorem 9.1, p.92 (PDF p.96): "Let G and H be two
finite groups of order N. There is an algorithm that computes the coset Iso(G, H) in time poly(N)";
p.92: "including computation of the isomorphism coset for groups given by their multiplication
tables"; §9.6, p.119 (PDF p.123): "These lifts and kernel generators generate Aut(G)".

There are one deterministic machine `M` and one constant `C` such that for every `N` and all groups
`G, H` of order `N`, labelled by `Fin N`, `M` on the two Cayley tables halts within `C·(N+1)^C` steps
and outputs a correct description of `Iso(G, H)`: emptiness if `G ≇ H`, otherwise an isomorphism `φ`
and automorphisms of `G` that generate `Aut(G)`, so that `Iso(G, H) = φ · Aut(G)`.

**Formalization Note.** Maps are output as tables of labels (`encIsoAnswer`). -/
theorem theorem_9_1 :
    ∃ M : Turing.TM2ComputableAux Bool Bool, ∃ C : ℕ,
      ∀ (N : ℕ) (G H : Type) [Group G] [Group H] (eG : G ≃ Fin N) (eH : H ≃ Fin N),
        ∃ ans : Option ((G ≃* H) × List (MulAut G)),
          CosetCorrect (Set.univ : Set (G ≃* H)) (Set.univ : Set (MulAut G)) ans ∧
            HMBinPacking.OutputsWithin M (encPair N (cayley eG) (cayley eH))
              (encIsoAnswer eG eH ans) (C * (N + 1) ^ C) := by sorry

end GroupIsoPoly
