-- Prove2me | Theorems.Thm_NeebLieExt_lemma_II_5
-- name    : NeebLieExt.lemma_II_5
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T17:19:14.439252+00:00
-- url     : https://prove2.me/theorems/32fecba6-4435-436b-b5fc-cdf79e8b0fab
-- title:
--   Lemma II.5 — $(n,x)\mapsto(\alpha(n)+\gamma(\beta(x)),\beta(x))$ is an isomorphism iff $(\alpha,\beta).(S,\omega)=\gamma.(S',\omega')$ (corrected: β(x) for the misprinted β(n))
-- statement:
--   Throughout, $\mathbb K$ is a topological field of characteristic $0$ (the discrete topology is allowed), topological vector spaces are Hausdorff, and $\mathfrak g$, $\mathfrak n$ are topological Lie algebras over $\mathbb K$.
--
--
--   Let $\alpha\in\mathrm{Aut}(\mathfrak n)$ and $\beta\in\mathrm{Aut}(\mathfrak g)$ be automorphisms (no continuity is needed), $\gamma\in C^1(\mathfrak g,\mathfrak n)$, let $S,S'\colon\mathfrak g\to\operatorname{der}\mathfrak n$ be linear and $\omega,\omega'\in C^2(\mathfrak g,\mathfrak n)$. Then the map
--   $$
--   \varphi\colon\mathfrak n\times\mathfrak g\to\mathfrak n\times\mathfrak g,\qquad (n,x)\mapsto\big(\alpha(n)+\gamma(\beta(x)),\ \beta(x)\big)
--   $$
--   is an isomorphism of Lie algebras $\mathfrak n\times_{(S,\omega)}\mathfrak g\to\mathfrak n\times_{(S',\omega')}\mathfrak g$ if and only if
--   $$
--   (\alpha,\beta).S=S'+\operatorname{ad}\circ\gamma\qquad\text{and}\qquad(\alpha,\beta).\omega:=\alpha\circ\omega\circ(\beta\times\beta)^{-1}=\omega'+d_{S'}\gamma+\tfrac12[\gamma,\gamma],
--   $$
--   where $((\alpha,\beta).S)(x):=\alpha\circ S(\beta^{-1}x)\circ\alpha^{-1}$; that is, $(\alpha,\beta).(S,\omega)=\gamma.(S',\omega')$.
--
--   With $\alpha=\mathrm{id}$, $\beta=\mathrm{id}$ this describes all equivalences between twisted products, and it is the step of Theorem II.7 showing that the fibres of $\Gamma$ are the $C^1(\mathfrak g,\mathfrak n)$-orbits.
--
--   **Formalization Note** Pointwise, the two conditions read $\alpha\big(S(\beta^{-1}x).\alpha^{-1}(m)\big)=S'(x).m+[\gamma(x),m]$ and $\alpha\big(\omega(\beta^{-1}x,\beta^{-1}y)\big)=\omega'(x,y)+(d_{S'}\gamma)(x,y)+[\gamma(x),\gamma(y)]$. "Isomorphism of Lie algebras" is "bijective and bracket preserving"; $\varphi$ is linear by construction.
--
--   Differences from the source:
--   - correction: φ(n, x) = (α(n) + γ(β(x)), β(n)) → φ(n, x) = (α(n) + γ(β(x)), β(x)); reason: β ∈ Aut(g) cannot be applied to n ∈ n, so the printed formula is not well formed (for n ≠ g it has no meaning at all); the proof on the same page computes φ([(n, x), (n′, x′)]) with second component β([x, x′]), i.e. with β(x)
--   - generalization: n ×_(S,ω) g and n ×_(S′,ω′) g for continuous factor systems (S, ω), (S′, ω′) → arbitrary linear S, S′ : g → der n and arbitrary ω, ω′ ∈ C²(g, n); reason: the bracket comparison uses only linearity and ω(x, 0) = 0; factor systems are a special case
--   - encoding: isomorphism of Lie algebras → φ bijective and φ(twistedBracket S ω p p′) = twistedBracket S′ ω′ (φ p) (φ p′); reason: φ is linear by construction
--   - generalization: (α, β) ∈ Aut(n) × Aut(g) → arbitrary Lie algebra automorphisms α, β, with no continuity assumed; reason: the bracket comparison is algebraic; automorphisms of topological Lie algebras (homeomorphic automorphisms) are a special case, so the statement holds under either reading of Aut
--   - encoding: (α, β).S = S′ + ad ∘ γ and (α, β).ω = ω′ + d_{S′}γ + ½[γ, γ] → the pointwise identities α(S(β⁻¹x)(α⁻¹m)) = S′(x)m + ⁅γ x, m⁆ and α(ω(β⁻¹x, β⁻¹y)) = gaugeω S′ ω′ γ x y; reason: the definitions of (α, β).S and (α, β).ω on p. 12
--   - encoding: ½[γ, γ] → (x, y) ↦ ⁅γ x, γ y⁆; reason: by the product formula on p. 5, [γ, γ](x, y) = [γx, γy] − [γy, γx] = 2[γx, γy]; same cochain
--   - encoding: cochain spaces C^p(g, V) and C¹_c(g, der n) → functions with the predicates IsCochain2/IsCochain3 (multilinear, alternating, jointly continuous) and linear S : g → LieDerivation K n n with (x, m) ↦ S(x)m jointly continuous; reason: the same sets; joint continuity makes each S(x) a continuous derivation
-- source:
--   Neeb, Non-abelian extensions of topological Lie algebras, arXiv:math/0411256v1, Lemma II.5, p. 12 (printed map (n, x) ↦ (α(n) + γ(β(x)), β(n)); the proof on p. 12 uses β(x))

import Mathlib
import Definitions.Def_NeebLieExt_IsTopLieAlgebra
import Definitions.Def_NeebLieExt_IsCochain2
import Definitions.Def_NeebLieExt_twistedBracket
import Definitions.Def_NeebLieExt_gaugeS

universe u v

namespace NeebLieExt

/-- **Lemma II.5 (which maps `(n, x) ↦ (α(n) + γ(β(x)), β(x))` are isomorphisms).** Neeb,
*Non-abelian extensions of topological Lie algebras*, arXiv:math/0411256v1, Lemma II.5, p. 12:
"Let (α, β) ∈ Aut(n) × Aut(g) and γ ∈ C¹(g, n). Then the map φ: n × g → n × g,
(n, x) ↦ (α(n) + γ(β(x)), β(n)) is an isomorphism of Lie algebras n ×_(S,ω) g → n ×_(S′,ω′) g if
and only if (α, β).S = S′ + ad ∘ γ and (α, β).ω := α ∘ ω ∘ (β × β)^{−1} = ω′ + d_{S′} γ + ½[γ, γ],
which means that (α, β).(S, ω) = γ.(S′, ω′). Here ((α, β).S)(x) := α ∘ (S(β^{−1}.x)) ∘ α^{−1}."

For Lie algebra automorphisms `α` of `n` and `β` of `g` and a continuous linear `γ : g → n`, the map `φ(a, x) = (α(a) + γ(β(x)), β(x))` is a bijection that carries the
bracket `twistedBracket S ω` to `twistedBracket S' ω'` if and only if
`α(S(β⁻¹x)(α⁻¹m)) = S′(x)m + ⁅γ(x), m⁆` for all `x, m` and
`α(ω(β⁻¹x, β⁻¹y)) = ω′(x, y) + (d_{S′}γ)(x, y) + ⁅γ(x), γ(y)⁆` for all `x, y`.

**Formalization Note** The printed second component `β(n)` is a misprint (`β ∈ Aut(g)` cannot be
applied to `n ∈ n`); the proof on the same page computes with `φ(n, x) = (α(n) + γ(β(x)), β(x))`,
which is what is stated. The lemma is stated for arbitrary linear `S, S′ : g → der n` and
arbitrary 2-cochains `ω, ω′ ∈ C²(g, n)`, not only factor systems; this specializes to the paper's
Lie algebras `n ×_(S,ω) g`. "Isomorphism of Lie algebras" is "bijective and bracket preserving"
(`φ` is linear by construction). `α`, `β` are arbitrary Lie algebra automorphisms; no
continuity is assumed, so the statement covers `Aut(n)`, `Aut(g)` read as automorphisms of
topological Lie algebras (the special case of homeomorphic automorphisms) as well as algebraic
ones. `½[γ, γ](x, y) = ⁅γ x, γ y⁆`, and the
right-hand side of the second condition is `gaugeω S' ω' γ`, with `d_{S′}`. -/
theorem lemma_II_5 {K : Type*} [Field K] [TopologicalSpace K] [IsTopologicalDivisionRing K] [CharZero K] {n : Type u} [LieRing n] [LieAlgebra K n] [TopologicalSpace n] [IsTopologicalAddGroup n] [ContinuousSMul K n] [T2Space n] [IsTopLieAlgebra n] {g : Type v} [LieRing g] [LieAlgebra K g] [TopologicalSpace g] [IsTopologicalAddGroup g] [ContinuousSMul K g] [T2Space g] [IsTopLieAlgebra g] (S S' : g →ₗ[K] LieDerivation K n n) (ω ω' : g → g → n) (hω : IsCochain2 K ω) (hω' : IsCochain2 K ω') (α : n ≃ₗ⁅K⁆ n) (β : g ≃ₗ⁅K⁆ g) (γ : g →L[K] n) :
    let φ : n × g → n × g := fun p => (α p.1 + γ (β p.2), β p.2)
    (Function.Bijective φ ∧
        ∀ p p' : n × g, φ (twistedBracket S ω p p') = twistedBracket S' ω' (φ p) (φ p')) ↔
      ((∀ (x : g) (m : n), α (S (β.symm x) (α.symm m)) = S' x m + ⁅γ x, m⁆) ∧
        (∀ x y : g, α (ω (β.symm x) (β.symm y)) = gaugeω S' ω' γ x y)) := by sorry

end NeebLieExt
