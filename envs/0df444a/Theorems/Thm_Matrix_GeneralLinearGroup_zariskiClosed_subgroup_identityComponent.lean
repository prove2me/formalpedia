-- Prove2me | Theorems.Thm_Matrix_GeneralLinearGroup_zariskiClosed_subgroup_identityComponent
-- name    : Matrix.GeneralLinearGroup.zariskiClosed_subgroup_identityComponent
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-11-25T16:21:26.553095+00:00
-- url     : https://prove2.me/theorems/79e12d4f-ccb7-5d23-ab93-b4f190ea99b1
-- title:
--   Identity component of a Zariski closed subgroup $G \le \mathrm{GL}_n(K)$: $G^\circ$ is closed, irreducible, normal of finite index, in every closed finite-index subgroup, trivial iff $G$ is finite
-- statement:
--   Let $K$ be any field and $n \ge 0$. View $\mathrm{GL}_n(K)$ as the affine variety $\{(A, A') \in M_n(K)^2 : A A' = 1\}$, with coordinates the entries of $g$ and of $g^{-1}$, and give it the **Zariski topology**: the closed sets are the common zero sets of sets of polynomials in these $2n^2$ coordinates. Let $G \le \mathrm{GL}_n(K)$ be a Zariski closed subgroup, with the subspace topology, and let $G^\circ$ be the irreducible component of $G$ containing $1$ (the **identity component**). Then $G^\circ$ is a subgroup of $\mathrm{GL}_n(K)$, and:
--
--   1. $G^\circ \subseteq G$, and $G^\circ$ is Zariski closed and irreducible;
--   2. $G^\circ$ is a normal subgroup of finite index in $G$;
--   3. $G^\circ \subseteq H$ for every Zariski closed subgroup $H \le \mathrm{GL}_n(K)$ such that $H \cap G$ has finite index in $G$;
--   4. $G$ is finite if and only if $G^\circ = \{1\}$.
--
--   Role: these are the basic structure facts on linear algebraic groups that reduce questions about an algebraic group to its connected part, for example for algebraic monodromy groups in Larsen's alternative, or in Zariski-density arguments for groups and semigroups of matrices (the intersection of a dense subgroup with $G^\circ$ is normal of finite index). The field $K$ is arbitrary (not necessarily algebraically closed): the statement is about the $K$-points with the induced Zariski topology, and the proof only uses that this space is Noetherian and $T_1$ and that translations and inversion are homeomorphisms. In part 3 closedness of $H$ matters: a non-closed subgroup of finite index need not contain $G^\circ$ (for $K = \mathbb{R}$, $G = \mathrm{GL}_1(\mathbb{R}) = \mathbb{R}^\times$ is irreducible, so $G^\circ = G$, while the positive reals form a subgroup of index $2$ that is not Zariski closed).
--
--   Proof idea: $\mathrm{GL}_n(K)$ embeds in $\mathrm{Spec}\, K[x_v]$, so it and every subspace are Noetherian; points are zero sets, so it is $T_1$; left and right translations, conjugations and inversion are polynomial in the coordinates, hence homeomorphisms. If $S, T \subseteq G$ are irreducible and contain $1$, then $S T$ is irreducible (multiplication is continuous in each variable separately), so $G^\circ G^\circ \subseteq G^\circ$ by maximality; similarly $(G^\circ)^{-1} = G^\circ$ and $g G^\circ g^{-1} = G^\circ$ for $g \in G$: $G^\circ$ is a normal subgroup, and it is closed in $G$ as an irreducible component, hence closed in $\mathrm{GL}_n(K)$ since $G$ is. The cosets $g G^\circ$ are irreducible components of $G$, and a Noetherian space has only finitely many, so the index is finite. If $H$ is closed and $H \cap G$ has finite index in $G$, its finitely many cosets in $G$ are closed, so $H \cap G$ is also open in $G$; then $H \cap G^\circ$ is a nonempty clopen subset of the irreducible (hence connected) space $G^\circ$, so $G^\circ \subseteq H$. Finally, if $G^\circ = \{1\}$ then $G$ is a finite union of cosets of $\{1\}$; conversely a finite $T_1$ space is discrete, so its irreducible components are points.
--
--   **Formalization Note**: $\mathrm{GL}_n(K)$ is `Matrix.GeneralLinearGroup n K` with rows and columns indexed by a finite type `n` ($n = $ `Fintype.card n`). The Zariski topology is the instance argument `τ`, pinned down by `hτ`: a set `Z` is closed iff there is a set `S` of polynomials in `MvPolynomial ((n × n) ⊕ (n × n)) K` with `g ∈ Z` iff every `p ∈ S` vanishes at the point of $K^{2n^2}$ whose coordinate `Sum.inl (i, j)` is the entry $g_{ij}$ and whose coordinate `Sum.inr (i, j)` is the entry $(g^{-1})_{ij}$. A topology is determined by its closed sets, so `hτ` determines `τ`; it only abbreviates this description. `hG` says $G$ is Zariski closed. In the conclusion `G` is also the type of its elements with the subspace topology, `irreducibleComponent (1 : G)` is Mathlib's irreducible component of $1$ in $G$ (the maximal irreducible subset containing $1$), and `Subtype.val ''` maps it into $\mathrm{GL}_n(K)$. The witness `G0` is $G^\circ$; it is unique, since a subgroup is determined by its underlying set, so the first conjunct says that $G^\circ$ is a subgroup and the remaining ones list its properties. `_root_.IsIrreducible` is Mathlib's topological `IsIrreducible` (the prefix only avoids `Matrix.IsIrreducible` from the theorem's namespace). `G0.subgroupOf G` is $G^\circ$ viewed as a subgroup of $G$, and `.Normal`, `.FiniteIndex` are normality and finite index in $G$; in part 3, `(H.subgroupOf G).FiniteIndex` says that $H \cap G$ has finite index in $G$. `Finite G` says that $G$ is a finite group, and `G0 = ⊥` says $G^\circ = \{1\}$. All types are in `Type`.
-- source:
--   A. Borel, Linear Algebraic Groups, 2nd ed., Graduate Texts in Mathematics 126, Springer 1991, Chapter I, Proposition 1.2; J. E. Humphreys, Linear Algebraic Groups, Graduate Texts in Mathematics 21, Springer 1975, Section 7.3; T. A. Springer, Linear Algebraic Groups, 2nd ed., Birkhauser 1998, Proposition 2.2.1

import Mathlib

set_option autoImplicit false

theorem Matrix.GeneralLinearGroup.zariskiClosed_subgroup_identityComponent
    (n : Type) [Fintype n] [DecidableEq n] (K : Type) [Field K]
    [τ : TopologicalSpace (Matrix.GeneralLinearGroup n K)]
    (hτ : ∀ Z : Set (Matrix.GeneralLinearGroup n K), IsClosed Z ↔
      ∃ S : Set (MvPolynomial ((n × n) ⊕ (n × n)) K), ∀ g : Matrix.GeneralLinearGroup n K,
        g ∈ Z ↔ ∀ p ∈ S, MvPolynomial.eval (Sum.elim (fun ij : n × n => (g : Matrix n n K) ij.1 ij.2)
          (fun ij : n × n => ((g⁻¹ : Matrix.GeneralLinearGroup n K) : Matrix n n K) ij.1 ij.2)) p = 0)
    (G : Subgroup (Matrix.GeneralLinearGroup n K))
    (hG : IsClosed (G : Set (Matrix.GeneralLinearGroup n K))) :
    ∃ G0 : Subgroup (Matrix.GeneralLinearGroup n K),
      (G0 : Set (Matrix.GeneralLinearGroup n K)) = Subtype.val '' irreducibleComponent (1 : G) ∧
      G0 ≤ G ∧ IsClosed (G0 : Set (Matrix.GeneralLinearGroup n K)) ∧
      _root_.IsIrreducible (G0 : Set (Matrix.GeneralLinearGroup n K)) ∧
      (G0.subgroupOf G).Normal ∧ (G0.subgroupOf G).FiniteIndex ∧
      (∀ H : Subgroup (Matrix.GeneralLinearGroup n K),
        IsClosed (H : Set (Matrix.GeneralLinearGroup n K)) → (H.subgroupOf G).FiniteIndex → G0 ≤ H) ∧
      (Finite G ↔ G0 = ⊥) := by
  sorry
