-- Prove2me | Theorems.Thm_NeebLieExt_lemma_II_4
-- name    : NeebLieExt.lemma_II_4
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T17:19:01.854491+00:00
-- url     : https://prove2.me/theorems/ea86c0d1-c161-457e-8782-f0e1b5fe458d
-- title:
--   Lemma II.4 — $\mathfrak n\times_{(S,\omega)}\mathfrak g$ is a topological Lie algebra and a split extension; every split extension is equivalent to one
-- statement:
--   Throughout, $\mathbb K$ is a topological field of characteristic $0$ (the discrete topology is allowed), topological vector spaces are Hausdorff, and $\mathfrak g$, $\mathfrak n$ are topological Lie algebras over $\mathbb K$.
--
--
--   1. Let $(S,\omega)$ be a continuous factor system and let $\mathfrak n\times_{(S,\omega)}\mathfrak g$ be the topological product vector space $\mathfrak n\times\mathfrak g$ with the bracket
--   $$
--   [(n,x),(n',x')]=\big([n,n']+S(x).n'-S(x').n+\omega(x,x'),\ [x,x']\big).
--   $$
--   Then this bracket is bilinear, alternating, satisfies the Jacobi identity and is continuous on $(\mathfrak n\times\mathfrak g)^2$, so $\mathfrak n\times_{(S,\omega)}\mathfrak g$ is a topological Lie algebra; the inclusion $n\mapsto(n,0)$ and the projection $q(n,x)=x$ are homomorphisms, and $q$ defines a topologically split extension of $\mathfrak g$ by $\mathfrak n$.
--   2. Conversely, every topologically split extension $\mathfrak n\hookrightarrow\widehat{\mathfrak g}\twoheadrightarrow\mathfrak g$ is equivalent to $\mathfrak n\times_{(S,\omega)}\mathfrak g$ for some continuous factor system $(S,\omega)$.
--
--   Part 1 makes the assignment $\Gamma(S,\omega)=[\mathfrak n\times_{(S,\omega)}\mathfrak g]$ well defined; part 2 says that $\Gamma$ is onto $\mathrm{Ext}(\mathfrak g,\mathfrak n)$.
--
--   **Formalization Note** The "topologically split extension" in part 1 is not restated: for the product topology the inclusion, the projection and the section $x\mapsto(0,x)$ are continuous, $\ker q$ is the image of the inclusion, and $(n,x)\mapsto(n,0)+(0,x)$ is the identity, independently of the bracket, so only the bracket facts carry content. Part 2 is literally clause (A) of Theorem II.7.
--
--   Differences from the source:
--   - encoding: n ×_(S,ω) g is a topological Lie algebra and q defines a topologically split extension → bilinearity, alternation, Jacobi identity and joint continuity of twistedBracket S ω on the product space, and bracket preservation by n ↦ (n, 0) and (n, x) ↦ x; reason: the remaining split-extension conditions hold for the product topology independently of the bracket, and Lean cannot install a second Lie bracket on n × g without a type synonym
--   - encoding: topologically split extension n ↪ ĝ ↠ g → IsTopSplitExt ι q: continuous ι, q, ι injective, ker q = im ι, and a continuous linear section σ with (n, x) ↦ ι(n) + σ(x) a homeomorphism; reason: p. 4's definition of split with ĝ/n identified with g through q
--   - encoding: equivalence of extensions → ExtEquivModel (a continuous Lie morphism n ×_(S,ω) g → E fixing n and commuting with the projections) and ModelEquiv (the same between two twisted products); reason: Definition II.1; the paper notes such a morphism is an isomorphism
--   - encoding: the paper's extensions ĝ (no size restriction) → topological Lie algebras E : Type w for an arbitrary universe w; reason: Lean needs a universe for E and the statement is universe-polymorphic in w, so it holds for every extension
--   - encoding: cochain spaces C^p(g, V) and C¹_c(g, der n) → functions with the predicates IsCochain2/IsCochain3 (multilinear, alternating, jointly continuous) and linear S : g → LieDerivation K n n with (x, m) ↦ S(x)m jointly continuous; reason: the same sets; joint continuity makes each S(x) a continuous derivation
-- source:
--   Neeb, Non-abelian extensions of topological Lie algebras, arXiv:math/0411256v1, Lemma II.4, p. 11

import Mathlib
import Definitions.Def_NeebLieExt_IsTopLieAlgebra
import Definitions.Def_NeebLieExt_twistedBracket
import Definitions.Def_NeebLieExt_IsFactorSystem
import Definitions.Def_NeebLieExt_IsTopSplitExt
import Definitions.Def_NeebLieExt_ExtEquivModel

universe u v w

namespace NeebLieExt

/-- **Lemma II.4 (continuous factor systems give exactly the topologically split extensions).**
Neeb, *Non-abelian extensions of topological Lie algebras*, arXiv:math/0411256v1, Lemma II.4,
p. 11: "For a continuous factor system (S, ω) let n ×_(S,ω) g be the topological product vector
space n × g endowed with the bracket (2.1). Then n ×_(S,ω) g is a topological Lie algebra and
q: n ×_(S,ω) g → g, (n, x) ↦ x defines a topologically split extension of g by n. Conversely,
every topologically split extension of g by n is equivalent to some n ×_(S,ω) g."

Part (a): for a continuous factor system `(S, ω)` the twisted bracket (2.1) is K-bilinear,
alternating, satisfies the Jacobi identity, is jointly continuous on `(n × g) × (n × g)`, and the
inclusion `a ↦ (a, 0)` and the projection `(a, x) ↦ x` preserve brackets. Part (b): every
topologically split extension `n →ι E →q g` (with `E` in any universe) is equivalent to
`n ×_(S,ω) g` for some continuous factor system `(S, ω)`.

**Formalization Note** `n × g` carries the product topology and module structure; Mathlib's
`⁅·, ·⁆` on `n × g` (the direct product) is not used. Part (a) lists the bracket axioms of a
topological Lie algebra (bilinear, alternating, Jacobi in Leibniz form, continuous) for
`twistedBracket S ω`. The split-extension part of (a) needs no statement beyond the two
bracket-preservation clauses: with the product topology, `a ↦ (a, 0)`, `(a, x) ↦ x` and the section
`x ↦ (0, x)` are continuous, `ker = im`, and `(a, x) ↦ (a, 0) + (0, x)` is the identity, so every
condition of `IsTopSplitExt` other than "ι and q are Lie homomorphisms" holds independently of
the bracket. Part (b) is syntactically clause (A) of `theorem_II_7`. -/
theorem lemma_II_4 {K : Type*} [Field K] [TopologicalSpace K] [IsTopologicalDivisionRing K] [CharZero K] {n : Type u} [LieRing n] [LieAlgebra K n] [TopologicalSpace n] [IsTopologicalAddGroup n] [ContinuousSMul K n] [T2Space n] [IsTopLieAlgebra n] {g : Type v} [LieRing g] [LieAlgebra K g] [TopologicalSpace g] [IsTopologicalAddGroup g] [ContinuousSMul K g] [T2Space g] [IsTopLieAlgebra g] :
    (∀ (S : g →ₗ[K] LieDerivation K n n) (ω : g → g → n), IsFactorSystem S ω →
      (∀ p : n × g, IsLinearMap K (twistedBracket S ω p)) ∧
      (∀ p' : n × g, IsLinearMap K (fun p => twistedBracket S ω p p')) ∧
      (∀ p : n × g, twistedBracket S ω p p = 0) ∧
      (∀ p p' p'' : n × g, twistedBracket S ω p (twistedBracket S ω p' p'') =
        twistedBracket S ω (twistedBracket S ω p p') p'' +
          twistedBracket S ω p' (twistedBracket S ω p p'')) ∧
      Continuous (fun pp : (n × g) × (n × g) => twistedBracket S ω pp.1 pp.2) ∧
      (∀ a b : n, twistedBracket S ω (a, 0) (b, 0) = (⁅a, b⁆, 0)) ∧
      (∀ p p' : n × g, (twistedBracket S ω p p').2 = ⁅p.2, p'.2⁆)) ∧
    (∀ (E : Type w) [LieRing E] [LieAlgebra K E] [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul K E] [IsTopLieAlgebra E] (ι : n →ₗ⁅K⁆ E) (q : E →ₗ⁅K⁆ g),
      IsTopSplitExt ι q → ∃ (S : g →ₗ[K] LieDerivation K n n) (ω : g → g → n), IsFactorSystem S ω ∧ ExtEquivModel ι q S ω) := by sorry

end NeebLieExt
