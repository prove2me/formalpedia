-- Prove2me | Theorems.Thm_ModularCurve_characterLattice_evalHom_surjective_and_trivial_iff_const
-- name    : ModularCurve.characterLattice_evalHom_surjective_and_trivial_iff_const
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:49.598281+00:00
-- url     : https://prove2.me/theorems/886eb443-55f9-5093-a98b-9c984d0c2648
-- title:
--   Characters of the degree-zero lattice are evaluations at node data
-- statement:
--   Let $S$ be a finite nonempty type and let $G$ be a commutative group. Write $\mathrm{characterLattice}\,S$ for the submodule of $S \to \mathbb{Z}$ consisting of those $a$ with $\sum_{s \in S} a(s) = 0$, i.e. the kernel of the $\mathbb{Z}$-linear form $\mathrm{degreeOn}\,S = \sum_{s} \mathrm{proj}_s$, and for $a$ in this lattice let $\mathrm{evalHom}\,a$ be the group homomorphism $(S \to G) \to G$ sending $w$ to $\prod_{s \in S} w(s)^{a(s)}$. The theorem asserts the conjunction of two statements. First, every additive homomorphism $\chi$ from $\mathrm{characterLattice}\,S$ to $\mathrm{Additive}\,G$ arises by evaluation: there is $w : S \to G$ such that for all $a$ in the lattice the multiplicative value of $\chi(a)$ equals $\prod_{s} w(s)^{a(s)}$. Second, for every $w : S \to G$, the associated character is trivial, i.e. $\prod_{s} w(s)^{a(s)} = 1$ for all $a$ in the lattice, if and only if $w$ is a constant function, i.e. $w = (\lambda\,\_ \mapsto c)$ for some $c \in G$. Together the two clauses say that evaluation induces a bijection between $(S \to G)$ modulo constants and $\mathrm{Hom}(\mathrm{characterLattice}\,S, G)$; no divisibility or torsion hypothesis on $G$ is needed.
--
--   This is the computation of the $G$-points of the torus whose character group is the degree-zero lattice $\mathbb{Z}[S]^{0}$ attached to a finite set $S$ of nodes: node data $w : S \to G$ modulo constants are exactly the characters of that lattice. It is used in the analysis of the component group and toric part of the Néron model at $p$, via [`ModularCurve.JHNeronObjectAtP.exists_addEquiv_toricPts_characterLattice_hom_of_ptsSp_nodeUnit`](thm.html#ModularCurve.JHNeronObjectAtP.exists_addEquiv_toricPts_characterLattice_hom_of_ptsSp_nodeUnit) and [`ModularCurve.JHNeronObjectAtP.toricPts_le_and_finPts_le_and_natCard_toricPts_mul_natCard_finPts_eq_of_coprime`](thm.html#ModularCurve.JHNeronObjectAtP.toricPts_le_and_finPts_le_and_natCard_toricPts_mul_natCard_finPts_eq_of_coprime).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_characterLattice_evalHom_surjective_and_trivial_iff_const.lean

import Mathlib
import Definitions.Def_ModularCurve_ComponentGroup
import Definitions.Def_ModularCurve_CharacterLatticePairings

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ModularCurve.characterLattice_evalHom_surjective_and_trivial_iff_const
    (S : Type*) [Fintype S] [Nonempty S] (G : Type*) [CommGroup G] :
    (∀ χ : ModularCurve.characterLattice S →+ Additive G,
        ∃ w : S → G, ∀ a, Additive.toMul (χ a) = ModularCurve.CharacterLattice.evalHom a w) ∧
    (∀ w : S → G, (∀ a : ModularCurve.characterLattice S, ModularCurve.CharacterLattice.evalHom a w = 1) ↔
        ∃ c : G, w = fun _ => c) := by sorry
