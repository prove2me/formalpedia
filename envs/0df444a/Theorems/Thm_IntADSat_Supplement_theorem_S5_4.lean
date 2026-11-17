-- Prove2me | Theorems.Thm_IntADSat_Supplement_theorem_S5_4
-- name    : IntADSat.Supplement.theorem_S5_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T08:58:27.906732+00:00
-- url     : https://prove2.me/theorems/0eb35819-417c-4624-ae1b-40e74504249c
-- title:
--   Theorem S5.4 — exact classification of a full principal moment fibre by graph-admissible overlattices
-- statement:
--   Let $G$ be an AD-full graph on $n\ge1$ vertices, $V=\mathbb Q^{V(G)}$ with its standard inner product, $\Lambda=\Lambda_G$, $\omega=e$ and $I=I_G$. The isomorphism classes in the principal moment fibre of $G$ are in bijection with its graph-admissible overlattices $\Lambda\subseteq L\subseteq\Lambda^\#$. Equivalently, they are the graph-admissible members of the finite set of $A,D$-stable isotropic subgroups of $D_\Lambda=\Lambda^\#/\Lambda$ of order $I$. In particular, each such overlattice contributes at most one graph isomorphism class.
--
--   Explicitly, the bijection sends the class of $H$ to $L_H=R\,\mathbb Z^{V(H)}$, where $R=Q^{\mathsf T}$ for the pointed rational orthogonal intertwiner $Q$ from $G$ to $H$:
--
--   1. every $H$ in the fibre has such a $Q$, and $L_H$ is graph-admissible;
--   2. two members $H,H'$ of the fibre give the same lattice if and only if $H\cong H'$;
--   3. every graph-admissible overlattice is $L_H$ for some $H$ in the fibre;
--   4. the set of $A,D$-stable isotropic subgroups of $D_\Lambda$ of order $I$ is finite;
--   5. for such a subgroup $S$ whose preimage $L_S$ in $\Lambda^\#$ satisfies conditions (1)–(3) of Definition S5.3, $L_S$ is a graph-admissible overlattice;
--   6. every graph-admissible overlattice is $L_S$ for such a subgroup $S$;
--   7. $S\mapsto L_S$ is injective.
--
--   The theorem reduces the reconstruction question for an AD-full graph to a finite lattice-theoretic realization problem.
--
--   Differences from the source:
--   - encoding: G a fixed AD-full graph (standing hypothesis of §S5); graphs have at least one vertex → finrank ℚ (wordModule ℚ G) = n and 0 < n; reason: Definition A.1 and the standing assumption (p.11)
--   - reading: the isomorphism classes of the fibre are in bijection with the graph-admissible overlattices → the paper's map [H] ↦ L_H = Qᵀℤ^m (rowLattice Q), stated as clauses (1) defined and admissible, (2) same lattice ↔ isomorphic, (3) onto; reason: these clauses say exactly that the map is a well-defined bijection on isomorphism classes; clause (1) also records the existence of Q (Theorem A.8)
--   - reading: equivalently, the graph-admissible members of the finite set of A,D-stable isotropic subgroups of D_Λ of order I → clauses (4) finiteness, (5)–(6) S ↦ preimage maps the graph-admissible members onto the graph-admissible overlattices, (7) injectivity; reason: the subgroup formulation via Lemma S5.1's correspondence S = L/Λ
--   - encoding: S stable under the induced endomorphisms; β(S,S) = 0; |S| = I → on representatives x ∈ Λ#: Ax, Dx ∈ Λ# with classes in S; ⟨x,y⟩ ∈ ℤ; Nat.card S = Nat.card (ℤⁿ/Λ_G); reason: the induced endomorphisms and the pairing are defined through representatives
--   - encoding: every vector of V_ω(L) is an eigenvector of D → ∃ c ∈ ℚ, Dv = cv for unit v; reason: unit vectors are nonzero
--   - encoding: the principal moment fibre of G (all finite simple graphs H with H ≡_μ G) → H : SimpleGraph (Fin m) for every m; reason: every finite simple graph is isomorphic to one on Fin m, and moments and isomorphism are invariant under relabelling; the empty-word moment forces m = n
-- source:
--   Z. Lu, Integral saturation of adjacency-degree lattices, arXiv:2611.01838 (held version, sha256 d1acbc32826e81e9ed42d927759ebc2d62786404cb2c44cedc931020e3631145), Theorem S5.4, p.42 (PDF 43); setting §S5, p.40 (PDF 41); Lemma S5.1 and Definition S5.3, p.41 (PDF 42)

import Mathlib
import Definitions.Def_IntADSat_wordModule
import Definitions.Def_IntADSat_Supplement_MomentEquiv
import Definitions.Def_IntADSat_Supplement_IsPointedIntertwiner
import Definitions.Def_IntADSat_Supplement_rowLattice
import Definitions.Def_IntADSat_Supplement_IsGraphAdmissible
import Definitions.Def_IntADSat_Supplement_discGroup
import Definitions.Def_IntADSat_Supplement_preLattice
import Definitions.Def_IntADSat_Supplement_IsStableIsotropicOfOrderI

set_option autoImplicit false

namespace IntADSat.Supplement

/-- **Theorem S5.4 (Exact classification of a full principal moment fibre)** (Z. Lu, *Integral saturation of adjacency-degree lattices*, arXiv:2611.01838 (held version, sha256 d1acbc32…3631145), p.42 (PDF 43); setting
§S5, p.40 (PDF 41), Lemma S5.1 and Definition S5.3, p.41 (PDF 42)). Let `G` be AD-full. The isomorphism
classes in the principal moment fibre of `G` are in bijection with its graph-admissible overlattices
`Λ ⊆ L ⊆ Λ^#`. Equivalently, they are the graph-admissible members of the finite set of `A, D`-stable
isotropic subgroups of `D_Λ` of order `I`. In particular, each such overlattice contributes at most one
graph isomorphism class.

**Formalization Note** The bijection is the paper's map `[H] ↦ L_H = Rℤ^{V(H)}`, `R = Qᵀ` for the pointed
intertwiner `Q` from `G` to `H` (`rowLattice Q`): (1) it is defined on the whole fibre and lands in the
graph-admissible lattices; (2) two fibre members have the same lattice iff they are isomorphic (well-defined
and injective on classes; the "only if" is "each overlattice contributes at most one class"); (3) it is onto.
The subgroup formulation: (4) the set of `A, D`-stable isotropic subgroups of order `I` is finite; (5) such a
subgroup whose preimage satisfies conditions (1)–(3) of Definition S5.3 (a graph-admissible subgroup) has a
graph-admissible preimage; (6) every graph-admissible lattice is the preimage of such a subgroup; (7) the
preimage map is injective. Fibre members range over all finite simple graphs (`Fin m`, every `m`). -/
theorem theorem_S5_4 {n : ℕ} (G : SimpleGraph (Fin n)) (hn : 0 < n)
    (hG : Module.finrank ℚ (IntADSat.wordModule ℚ G) = n) :
    (∀ (m : ℕ) (H : SimpleGraph (Fin m)), MomentEquiv G H →
      (∃ Q : Matrix (Fin m) (Fin n) ℚ, IsPointedIntertwiner G H Q) ∧
      ∀ Q : Matrix (Fin m) (Fin n) ℚ, IsPointedIntertwiner G H Q →
        IsGraphAdmissible G (rowLattice Q)) ∧
    (∀ (m m' : ℕ) (H : SimpleGraph (Fin m)) (H' : SimpleGraph (Fin m'))
        (Q : Matrix (Fin m) (Fin n) ℚ) (Q' : Matrix (Fin m') (Fin n) ℚ),
      MomentEquiv G H → MomentEquiv G H' → IsPointedIntertwiner G H Q → IsPointedIntertwiner G H' Q' →
      (rowLattice Q = rowLattice Q' ↔ Nonempty (H ≃g H'))) ∧
    (∀ L : Submodule ℤ (Fin n → ℚ), IsGraphAdmissible G L →
      ∃ (m : ℕ) (H : SimpleGraph (Fin m)) (Q : Matrix (Fin m) (Fin n) ℚ),
        MomentEquiv G H ∧ IsPointedIntertwiner G H Q ∧ rowLattice Q = L) ∧
    {S : Submodule ℤ (discGroup G) | IsStableIsotropicOfOrderI G S}.Finite ∧
    (∀ S : Submodule ℤ (discGroup G), IsStableIsotropicOfOrderI G S →
      UnitFrameConditions G (preLattice G S) → IsGraphAdmissible G (preLattice G S)) ∧
    (∀ L : Submodule ℤ (Fin n → ℚ), IsGraphAdmissible G L →
      ∃ S : Submodule ℤ (discGroup G), IsStableIsotropicOfOrderI G S ∧ preLattice G S = L) ∧
    (∀ S S' : Submodule ℤ (discGroup G), preLattice G S = preLattice G S' → S = S') := by sorry

end IntADSat.Supplement
