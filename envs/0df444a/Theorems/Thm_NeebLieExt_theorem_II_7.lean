-- Prove2me | Theorems.Thm_NeebLieExt_theorem_II_7
-- name    : NeebLieExt.theorem_II_7
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T17:19:46.129655+00:00
-- url     : https://prove2.me/theorems/7e78b560-12b5-4322-8975-92d8bf53d5c9
-- title:
--   Theorem II.7 — $\mathrm{Ext}(\mathfrak g,\mathfrak n)\cong Z^2/C^1$, and each $\mathrm{Ext}(\mathfrak g,\mathfrak n)_{[S]}$ is an affine space over $H^2(\mathfrak g,\mathfrak z(\mathfrak n))_S$
-- statement:
--   Throughout, $\mathbb K$ is a topological field of characteristic $0$ (the discrete topology is allowed), topological vector spaces are Hausdorff, and $\mathfrak g$, $\mathfrak n$ are topological Lie algebras over $\mathbb K$.
--
--
--   The assignment
--   $$
--   \Gamma\colon Z^2(\mathfrak g,\mathfrak n)\to\mathrm{Ext}(\mathfrak g,\mathfrak n),\qquad (S,\omega)\mapsto[\mathfrak n\times_{(S,\omega)}\mathfrak g]
--   $$
--   factors through a bijection $\overline\Gamma\colon Z^2(\mathfrak g,\mathfrak n)/C^1(\mathfrak g,\mathfrak n)\to\mathrm{Ext}(\mathfrak g,\mathfrak n)$. For every continuous outer action $S$ of $\mathfrak g$ on $\mathfrak n$, the map
--   $$
--   Z^2(\mathfrak g,\mathfrak n)_S\to\mathrm{Ext}(\mathfrak g,\mathfrak n)_{[S]},\qquad \omega\mapsto[\mathfrak n\times_{(S,\omega)}\mathfrak g]
--   $$
--   is surjective and its fibres are the cosets of $B^2(\mathfrak g,\mathfrak z(\mathfrak n))_S$ in the affine space $Z^2(\mathfrak g,\mathfrak n)_S$ with translation group $Z^2(\mathfrak g,\mathfrak z(\mathfrak n))_S$. Thus $\mathrm{Ext}(\mathfrak g,\mathfrak n)_{[S]}$ is an affine space with translation group $H^2(\mathfrak g,\mathfrak z(\mathfrak n))_S$.
--
--   Spelled out, the statement consists of:
--
--   1. (A) Every topologically split extension of $\mathfrak g$ by $\mathfrak n$ is equivalent to $\mathfrak n\times_{(S,\omega)}\mathfrak g$ for some $(S,\omega)\in Z^2(\mathfrak g,\mathfrak n)$.
--   2. (B0) $Z^2(\mathfrak g,\mathfrak n)$ is invariant under the action $\gamma.(S,\omega)$ of $C^1(\mathfrak g,\mathfrak n)$.
--   3. (B) For $(S,\omega),(S',\omega')\in Z^2(\mathfrak g,\mathfrak n)$: $\mathfrak n\times_{(S,\omega)}\mathfrak g\sim\mathfrak n\times_{(S',\omega')}\mathfrak g$ if and only if $(S,\omega)=\gamma.(S',\omega')$ for some $\gamma\in C^1(\mathfrak g,\mathfrak n)$.
--   4. (C1) For a continuous outer action $S$, every extension with continuous $\mathfrak g$-kernel $[S]$ is equivalent to $\mathfrak n\times_{(S,\omega)}\mathfrak g$ for some $\omega\in Z^2(\mathfrak g,\mathfrak n)_S$.
--   5. (C2) For $\omega,\omega'\in Z^2(\mathfrak g,\mathfrak n)_S$: $\mathfrak n\times_{(S,\omega)}\mathfrak g\sim\mathfrak n\times_{(S,\omega')}\mathfrak g$ if and only if $\omega-\omega'\in B^2(\mathfrak g,\mathfrak z(\mathfrak n))_S$.
--   6. (C3) For $\omega\in Z^2(\mathfrak g,\mathfrak n)_S$: $\omega+\beta\in Z^2(\mathfrak g,\mathfrak n)_S$ if and only if $\beta\in Z^2(\mathfrak g,\mathfrak z(\mathfrak n))_S$.
--   7. (C4) For every base point $\omega_0\in Z^2(\mathfrak g,\mathfrak n)_S$, every extension with $\mathfrak g$-kernel $[S]$ is equivalent to $\mathfrak n\times_{(S,\omega_0+\beta)}\mathfrak g$ for some $\beta\in Z^2(\mathfrak g,\mathfrak z(\mathfrak n))_S$, and for $\beta,\beta'\in Z^2(\mathfrak g,\mathfrak z(\mathfrak n))_S$ the two twisted products are equivalent if and only if $\beta-\beta'\in B^2(\mathfrak g,\mathfrak z(\mathfrak n))_S$; that is, $H^2(\mathfrak g,\mathfrak z(\mathfrak n))_S$ acts simply transitively on $\mathrm{Ext}(\mathfrak g,\mathfrak n)_{[S]}$ (Corollary II.8).
--
--   The theorem describes $\mathrm{Ext}(\mathfrak g,\mathfrak n)$ as the disjoint union over continuous $\mathfrak g$-kernels $[S]$ of affine spaces over $H^2(\mathfrak g,\mathfrak z(\mathfrak n))_S$, extending the classical description of abelian extensions by $H^2$ to non-abelian kernels and to topologically split extensions of topological Lie algebras.
--
--   **Formalization Note** $\mathrm{Ext}(\mathfrak g,\mathfrak n)$ and $H^2$ are not built as quotients: the bijection $\overline\Gamma$ is (B0) + (A) + (B), and the affine structure is (C3) + (C4) relative to a base point.
--
--   Differences from the source:
--   - generalization: for every continuous outer action S with Ext(g, n)_[S] ≠ Ø → for every continuous outer action S; reason: if Ext(g, n)_[S] = Ø then Z²(g, n)_S = Ø (each ω ∈ Z²(g, n)_S gives the extension n ×_(S,ω) g with kernel [S], by Lemma II.4), so (C1)–(C4) hold vacuously; with the hypothesis the clauses are the paper's
--   - encoding: Γ factors through a bijection Γ̄: Z²(g, n)/C¹(g, n) → Ext(g, n) → (B0) Z²(g, n) is C¹(g, n)-invariant, (A) every extension is equivalent to some n ×_(S,ω) g, (B) two twisted products are equivalent iff the factor systems lie in one C¹(g, n)-orbit; reason: Γ̄ exists and is a bijection exactly when Γ is onto and its fibres are the orbits; Ext(g, n) is not built as a quotient type
--   - encoding: Z²(g, n)_S → Ext(g, n)_[S] is surjective, its fibers are the cosets of B²(g, z(n))_S in the affine space Z²(g, n)_S with translation group Z²(g, z(n))_S → (C1) onto Ext(g, n)_[S]; (C2) ω ∼ ω′ iff ω − ω′ ∈ B²(g, z(n))_S; (C3) ω + β ∈ Z²(g, n)_S iff β ∈ Z²(g, z(n))_S; reason: the three clauses are the three assertions of the sentence
--   - encoding: Ext(g, n)_[S] is an affine space with translation group H²(g, z(n))_S → (C4) for a base point ω₀ ∈ Z²(g, n)_S, β ↦ [n ×_(S,ω₀+β) g] maps Z²(g, z(n))_S onto Ext(g, n)_[S] and identifies β, β′ exactly when β − β′ ∈ B²(g, z(n))_S; reason: this is the simply transitive action of H² = Z²/B² of Corollary II.8, stated without the quotient
--   - encoding: Ext(g, n)_[S] (extension classes with continuous g-kernel [S]) → extensions satisfying HasKernel ι q S: ad(σ(x))|_n = S(x) + ad(γ(x)) for a continuous linear section σ and some γ ∈ Lin(g, n); reason: Definition II.2's S ∼ S′, written through ι
--   - encoding: z(n)-valued cochains and the g-module z(n) → n-valued cochains with central values, with the same differential d_S; reason: Definition II.2: x.z := S(x).z
--   - encoding: topologically split extension n ↪ ĝ ↠ g → IsTopSplitExt ι q: continuous ι, q, ι injective, ker q = im ι, and a continuous linear section σ with (n, x) ↦ ι(n) + σ(x) a homeomorphism; reason: p. 4's definition of split with ĝ/n identified with g through q
--   - encoding: equivalence of extensions → ExtEquivModel (a continuous Lie morphism n ×_(S,ω) g → E fixing n and commuting with the projections) and ModelEquiv (the same between two twisted products); reason: Definition II.1; the paper notes such a morphism is an isomorphism
--   - encoding: the paper's extensions ĝ (no size restriction) → topological Lie algebras E : Type w for an arbitrary universe w; reason: Lean needs a universe for E and the statement is universe-polymorphic in w, so it holds for every extension
--   - encoding: ½[γ, γ] → (x, y) ↦ ⁅γ x, γ y⁆; reason: by the product formula on p. 5, [γ, γ](x, y) = [γx, γy] − [γy, γx] = 2[γx, γy]; same cochain
--   - encoding: cochain spaces C^p(g, V) and C¹_c(g, der n) → functions with the predicates IsCochain2/IsCochain3 (multilinear, alternating, jointly continuous) and linear S : g → LieDerivation K n n with (x, m) ↦ S(x)m jointly continuous; reason: the same sets; joint continuity makes each S(x) a continuous derivation
--   - reading: "The assignment Γ: Z²(g, n) → Ext(g, n), (S, ω) ↦ [n ×_(S,ω) g]" (Γ lands in Ext(g, n), i.e. each n ×_(S,ω) g is a topologically split extension) → not restated in this item; reason: the theorem presupposes this well-definedness from Lemma II.4 and asserts only the factorization through a bijection and the affine structure; the well-definedness is stated in full as the milestone NeebLieExt.lemma_II_4 (part 1)
-- source:
--   Neeb, Non-abelian extensions of topological Lie algebras, arXiv:math/0411256v1, Theorem II.7, p. 13; Corollary II.8, p. 13

import Mathlib
import Definitions.Def_NeebLieExt_IsTopLieAlgebra
import Definitions.Def_NeebLieExt_gaugeS
import Definitions.Def_NeebLieExt_IsFactorSystem
import Definitions.Def_NeebLieExt_InZ2Center
import Definitions.Def_NeebLieExt_IsTopSplitExt
import Definitions.Def_NeebLieExt_ExtEquivModel
import Definitions.Def_NeebLieExt_HasKernel

universe u v w

namespace NeebLieExt

/-- **Theorem II.7 (classification of topologically split extensions).** Neeb, *Non-abelian
extensions of topological Lie algebras*, arXiv:math/0411256v1, Theorem II.7, p. 13: "The
assignment Γ: Z²(g, n) → Ext(g, n), (S, ω) ↦ [n ×_(S,ω) g] factors through a bijection
Γ̄: Z²(g, n)/C¹(g, n) → Ext(g, n). For every continuous outer action S of g on n with
Ext(g, n)_[S] ≠ Ø the map Z²(g, n)_S → Ext(g, n)_[S], ω ↦ [n ×_(S,ω) g] is surjective and its
fibers are the cosets of B²(g, z(n))_S in the affine space Z²(g, n)_S with translation group
Z²(g, z(n))_S. Thus Ext(g, n)_[S] inherits the structure of an affine space with translation group
H²(g, z(n))_S."

Clauses: (A) every topologically split extension of `g` by `n` is equivalent to `n ×_(S,ω) g` for
some continuous factor system (Γ is onto); (B0) `Z²(g, n)` is invariant under the gauge action of
`C¹(g, n)`; (B) `n ×_(S,ω) g` and `n ×_(S′,ω′) g` are equivalent iff `(S, ω) = γ.(S′, ω′)` for some
`γ ∈ C¹(g, n)` (the fibres of Γ are the orbits, so Γ induces a bijection `Z²/C¹ → Ext`); and, for
each continuous outer action `S`: (C1) every extension with continuous g-kernel `[S]` is
equivalent to `n ×_(S,ω) g` for some `ω ∈ Z²(g, n)_S`; (C2) for `ω, ω′ ∈ Z²(g, n)_S`,
`n ×_(S,ω) g ∼ n ×_(S,ω′) g` iff `ω − ω′ ∈ B²(g, z(n))_S`; (C3) for `ω ∈ Z²(g, n)_S`,
`ω + β ∈ Z²(g, n)_S` iff `β ∈ Z²(g, z(n))_S`; (C4) for any base point `ω₀ ∈ Z²(g, n)_S`, the map
`β ↦ [n ×_(S,ω₀+β) g]` from `Z²(g, z(n))_S` is onto `Ext(g, n)_[S]` and identifies exactly the `β`
that differ by an element of `B²(g, z(n))_S`, i.e. `H²(g, z(n))_S` acts simply transitively.

**Formalization Note** `Ext(g, n)` is not built as a quotient type: the bijection `Γ̄` is stated
as (B0) + (A) + (B), with extensions `E` ranging over an arbitrary universe `w`, and the affine
structure over `H²(g, z(n))_S = Z²/B²` as (C3) + (C4) through a base point. The hypothesis
`Ext(g, n)_[S] ≠ Ø` is dropped: without it every clause still holds (if no extension has kernel
`[S]`, then `Z²(g, n)_S` is empty by Lemma II.4). "Topologically split" is unfolded in
`IsTopSplitExt`, the g-kernel condition in `HasKernel`, equivalence in `ExtEquivModel` and
`ModelEquiv`. -/
theorem theorem_II_7 {K : Type*} [Field K] [TopologicalSpace K] [IsTopologicalDivisionRing K] [CharZero K] {n : Type u} [LieRing n] [LieAlgebra K n] [TopologicalSpace n] [IsTopologicalAddGroup n] [ContinuousSMul K n] [T2Space n] [IsTopLieAlgebra n] {g : Type v} [LieRing g] [LieAlgebra K g] [TopologicalSpace g] [IsTopologicalAddGroup g] [ContinuousSMul K g] [T2Space g] [IsTopLieAlgebra g] :
    (∀ (E : Type w) [LieRing E] [LieAlgebra K E] [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul K E] [IsTopLieAlgebra E] (ι : n →ₗ⁅K⁆ E) (q : E →ₗ⁅K⁆ g),
      IsTopSplitExt ι q → ∃ (S : g →ₗ[K] LieDerivation K n n) (ω : g → g → n), IsFactorSystem S ω ∧ ExtEquivModel ι q S ω) ∧
    (∀ (S : g →ₗ[K] LieDerivation K n n) (ω : g → g → n) (γ : g →L[K] n),
      IsFactorSystem S ω → IsFactorSystem (gaugeS S γ) (gaugeω S ω γ)) ∧
    (∀ (S : g →ₗ[K] LieDerivation K n n) (ω : g → g → n) (S' : g →ₗ[K] LieDerivation K n n) (ω' : g → g → n),
      IsFactorSystem S ω → IsFactorSystem S' ω' →
        (ModelEquiv S ω S' ω' ↔ ∃ γ : g →L[K] n, S = gaugeS S' γ ∧ ω = gaugeω S' ω' γ)) ∧
    (∀ S : g →ₗ[K] LieDerivation K n n, IsContOuterAction S →
      (∀ (E : Type w) [LieRing E] [LieAlgebra K E] [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul K E] [IsTopLieAlgebra E] (ι : n →ₗ⁅K⁆ E) (q : E →ₗ⁅K⁆ g),
        IsTopSplitExt ι q → HasKernel ι q S → ∃ ω : g → g → n, InZ2S S ω ∧ ExtEquivModel ι q S ω) ∧
      (∀ ω ω' : g → g → n, InZ2S S ω → InZ2S S ω' →
        (ModelEquiv S ω S ω' ↔ InB2Center S (ω - ω'))) ∧
      (∀ ω β : g → g → n, InZ2S S ω → (InZ2S S (ω + β) ↔ InZ2Center S β)) ∧
      (∀ ω₀ : g → g → n, InZ2S S ω₀ →
        (∀ (E : Type w) [LieRing E] [LieAlgebra K E] [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul K E] [IsTopLieAlgebra E] (ι : n →ₗ⁅K⁆ E) (q : E →ₗ⁅K⁆ g),
          IsTopSplitExt ι q → HasKernel ι q S → ∃ β : g → g → n, InZ2Center S β ∧ ExtEquivModel ι q S (ω₀ + β)) ∧
        (∀ β β' : g → g → n, InZ2Center S β → InZ2Center S β' →
          (ModelEquiv S (ω₀ + β) S (ω₀ + β') ↔ InB2Center S (β - β'))))) := by sorry

end NeebLieExt
