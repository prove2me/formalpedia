-- Prove2me | Theorems.Thm_GroupIsoPoly_bcq12_coset
-- name    : GroupIsoPoly.bcq12_coset
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T02:54:03.341571+00:00
-- url     : https://prove2.me/theorems/0e4fb7e5-0969-4cd6-9bf8-9271ea916da9
-- title:
--   [BCQ12] — the isomorphism coset of groups with trivial solvable radical in time $\mathrm{poly}(N)$
-- statement:
--   There are a deterministic algorithm and a constant $C$ with the following property. For every $N$ and all groups $G,H$ of order $N$ with trivial solvable radicals ($\mathrm{srad}(G)=\mathrm{srad}(H)=1$), given by Cayley tables under arbitrary labellings, the algorithm halts within $C(N+1)^C$ steps and outputs the isomorphism coset: emptiness if $G\not\cong H$, and otherwise an isomorphism $\varphi:G\to H$ together with automorphisms of $G$ that generate $\mathrm{Aut}(G)$, so that
--   $$
--   \mathrm{Iso}(G,H)=\varphi\cdot\mathrm{Aut}(G).
--   $$
--
--   This is the terminal case of the group isomorphism recursion (§9.6): after the elementary abelian layers of $\mathrm{srad}(G)$ have been processed, the quotient $G/\mathrm{srad}(G)$ is handled by the algorithm of Babai, Codenotti and Qiao for groups without abelian normal subgroups. It is a cited result; the paper does not prove it.
--
--   **Formalization Note** Inputs outside the promise ($\mathrm{srad}\ne1$) are unconstrained. The machine is a Mathlib multi-stack Turing machine run through the published `HMBinPacking.OutputsWithin`.
--
--   Differences from the source:
--
--   - reading: "an algorithm … in time polynomial in N" → one deterministic Mathlib TM2 machine `M` and one constant `C`, chosen before `N` and the groups, halting within `C·(N+1)^C` steps on every input pair; reason: the input has length Θ(N² log N), so poly(N) is poly(input length); Turing machines and RAMs simulate each other with polynomial overhead
--   - encoding: "given by their Cayley (multiplication) tables" → every labelling `G ≃ Fin N`, `H ≃ Fin N` of groups in `Type`, the tables coded row-major with `encodeNat` (`encPair`); reason: any standard table code differs polynomially; quantifying over every labelling is what "given by" means; every finite group is isomorphic to one in `Type`
--   - reading: "computes the coset Iso(G, H)" → an output coding emptiness iff `G ≇ H`, else an isomorphism `φ` and a list of automorphisms generating all of `Aut(G)` (`CosetCorrect` with `Trans = Iso(G,H)`, `Stab = Aut(G)`); reason: Iso(G, H) = φ·Aut(G); §9.6, p.119: "These lifts and kernel generators generate Aut(G)"
--   - reading: output elements with straight-line programs in the input generators (§3.5, p.19) → output elements written as themselves (label tables, matrix entries, permutation images); reason: for permutation and matrix groups each form is computable from the other in polynomial time (constructive membership, §3.5 (i), p.20); the coset is the same
--   - encoding: "groups with trivial solvable radical" / "groups without abelian normal subgroups" (p.4) → srad G = ⊥ and srad H = ⊥ as hypotheses; reason: for finite groups the two conditions coincide (a nontrivial solvable normal subgroup contains a nontrivial abelian characteristic subgroup); a promise, so other inputs are unconstrained
-- source:
--   Qiao, Zhang, Testing isomorphism of finite groups in time polynomial in the group order, preprint, Nov. 3, 2026 (held version sha256 eb9a3355…), cited in §9.2, p.94 (PDF p.98) and §9.6, p.118 (PDF p.122); §1.5, p.4 (PDF p.8)

import Mathlib
import Definitions.Def_HMBinPacking_OutputsWithin
import Definitions.Def_GroupIsoPoly_encPair
import Definitions.Def_GroupIsoPoly_CosetCorrect
import Definitions.Def_GroupIsoPoly_encIsoAnswer
import Definitions.Def_GroupIsoPoly_srad

set_option autoImplicit false

namespace GroupIsoPoly

/-- **[BCQ12] — the isomorphism coset of groups with trivial solvable radical in polynomial time.**

Qiao, Zhang, *Testing isomorphism of finite groups in time polynomial in the group order*, preprint,
Nov. 3, 2026 (held version sha256 eb9a3355…), cited in §9.2, p.94 (PDF p.98): "The group recursion
stops at the quotient by the solvable radical, where the algorithm of Babai, Codenotti, and Qiao
applies [BCQ12]; its full-coset output is recorded in [GQ15a, Introduction and proof of
Corollary 2]"; §9.6, p.118 (PDF p.122): "The only terminal group-isomorphism algorithm required is
that of Babai, Codenotti, and Qiao [BCQ12] for groups with trivial solvable radical. Its
polynomial-time computation of the full isomorphism coset is explicitly recorded".

There are one deterministic machine `M` and one constant `C` such that for every `N` and all groups
`G, H` of order `N` with trivial solvable radicals, labelled by `Fin N`, `M` on the two Cayley tables
halts within `C·(N+1)^C` steps and outputs a correct description of `Iso(G, H)`: emptiness if
`G ≇ H`, otherwise an isomorphism `φ` and automorphisms of `G` that generate `Aut(G)`, so that
`Iso(G, H) = φ · Aut(G)`.

**Formalization Note.** A cited result, not proved in the paper. Inputs outside the promise
(`srad G ≠ 1` or `srad H ≠ 1`) are unconstrained. -/
theorem bcq12_coset :
    ∃ M : Turing.TM2ComputableAux Bool Bool, ∃ C : ℕ,
      ∀ (N : ℕ) (G H : Type) [Group G] [Group H] (eG : G ≃ Fin N) (eH : H ≃ Fin N),
        srad G = ⊥ → srad H = ⊥ →
        ∃ ans : Option ((G ≃* H) × List (MulAut G)),
          CosetCorrect (Set.univ : Set (G ≃* H)) (Set.univ : Set (MulAut G)) ans ∧
            HMBinPacking.OutputsWithin M (encPair N (cayley eG) (cayley eH))
              (encIsoAnswer eG eH ans) (C * (N + 1) ^ C) := by sorry

end GroupIsoPoly
