-- Prove2me | Theorems.Thm_OAI_EilenbergGanea_boundary_basis_small_transport
-- name    : OAI.EilenbergGanea.boundary_basis_small_transport
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-25T00:16:47.195999+00:00
-- url     : https://prove2.me/theorems/0df3823b-641f-45bf-9b30-9dec6cefd3c1
-- title:
--   Theorem 3.1 (the presentation comparison theorem), algebraic form: small SU(2) edge labels trivial on a boundary basis are trivial on every closed path (OpenAI)
-- statement:
--   The paper's Theorem 3.1, the presentation comparison theorem (p. 7: "Suppose that $\Gamma$ is residually finite and that $\mathcal D$ is a finite indexed list of words on $S$, trivial in $\Gamma$, whose chains form a free $\Lambda$-basis of $\ker \partial_1$. … If $\Gamma$ admits a $K(\Gamma, 1)$ of dimension at most two, there is an $\eta > 0$ with the following property. Assign a label in $H = \mathrm{SU}(2)$ to every oriented generator edge, assign the inverse label to its reverse, and assume that every label has distance less than $\eta$ from 1. If the product along every translate of every $z \in \mathcal D$ is 1, then the product along every closed edge path is 1."), in the algebraic form OpenAI formalized. It is an intermediate statement of the split of OpenAI's proof of `OAI.EilenbergGanea.source_main`.
--
--   **How it differs from the printed theorem.** The hypothesis "$\Gamma$ admits a $K(\Gamma, 1)$ of dimension at most two" is replaced by its algebraic consequence, an aspherical presentation: generators `a₀ : A → Γ` and relators `r₀ : R → FreeGroup A` presenting $\Gamma$ whose translated relator chains form a $\mathbb Z$-basis of the cycles of the Cayley graph. OpenAI derives such a presentation from a two-dimensional classifying space separately (`CWComplex/Presentation.lean`); here $A$ and $R$ may have any cardinality. Labels are given only on the positively oriented edges (a label on the reverse edge is the inverse by construction of the path product).
--
--   **Notation** (from the definitions bundles of this split). `SU2` is the unit quaternions. For `v : S → Γ`, `wordValue v : FreeGroup S →* Γ` evaluates words; `BasedChains Γ S` is the free abelian group on $\Gamma \times S$ (the edges of the Cayley graph, $(g, s)$ running from $g$ to $g\,v(s)$), and `cycles v` is the kernel of its boundary map to $\mathbb Z[\Gamma]$. `relatorChainMap v z` sends the basis element $(g, i)$ to the edge chain of the path spelling $z_i$ from $g$. `pathProduct v a w g` is the product, in order, of the labels `a` along the path that spells $w$ from vertex $g$ (inverse labels on inverse letters).
--
--   **The statement.** Let $\Gamma$ be residually finite, $Z$ finite, `v : S → Γ` with `wordValue v` surjective, and words `z : Z → FreeGroup S` trivial in $\Gamma$ such that `relatorChainMap v z` is (as `B`) an isomorphism onto `cycles v`. Given an aspherical presentation `(a₀, r₀)` of $\Gamma$ as above (with its basis isomorphism `E`), there is $\eta > 0$ such that every labelling `a : Γ → S → SU2` with $\|a(g,s) - 1\| < \eta$ for all $g, s$ and `pathProduct v a (z i) g = 1` for all $i, g$ has `pathProduct v a w g = 1` for every word $w$ with `wordValue v w = 1` and every $g$.
-- source:
--   OpenAI, A finitely generated counterexample to the Eilenberg–Ganea conjecture, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 249; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-finitely-generated-counterexample-to-the-Eilenberg-Ganea-conjecture-September-23-2026/paper.pdf, Theorem 3.1, p. 7; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Topology/EilenbergGanea/PresentationAlignment.lean (declaration OAI.EilenbergGanea.boundary_basis_small_transport)

import Mathlib
import Definitions.Def_OAIEG011

section

attribute [-instance] _root_.OAI.EilenbergGanea.CWCollar.positiveRealsContractible
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open Classical Set Filter Topology MeasureTheory
open scoped Quaternion ContDiff

namespace EilenbergGanea
open scoped Quaternion
section BoundaryBasisTransport
variable {Γ S Z A R : Type*} [Group Γ] [Group.ResiduallyFinite Γ] [Fintype Z]

theorem boundary_basis_small_transport
    (v : S → Γ) (hv : Function.Surjective (wordValue v))
    (z : Z → FreeGroup S) (hz : ∀ i, wordValue v (z i) = 1)
    (B : BasedChains Γ Z ≃ₗ[ℤ] cycles v)
    (hB : ∀ c, (B c : BasedChains Γ S) = relatorChainMap v z c)
    (a₀ : A → Γ) (ha₀ : Function.Surjective (wordValue a₀))
    (r₀ : R → FreeGroup A) (hr₀ : ∀ i, wordValue a₀ (r₀ i) = 1)
    (hp₀ : (wordValue a₀).ker = Subgroup.normalClosure (Set.range r₀))
    (E : BasedChains Γ R ≃ₗ[ℤ] cycles a₀)
    (hE : ∀ c, (E c : BasedChains Γ A) = relatorChainMap a₀ r₀ c) :
    ∃ η : ℝ, 0 < η ∧ ∀ a : Γ → S → SU2,
      (∀ g s, ‖(a g s : ℍ)-1‖ < η) →
      (∀ i g, pathProduct v a (z i) g = 1) →
      ∀ w : FreeGroup S, wordValue v w = 1 → ∀ g,
        pathProduct v a w g = 1 := by
  sorry

end BoundaryBasisTransport
end EilenbergGanea

end

end OAI
end
