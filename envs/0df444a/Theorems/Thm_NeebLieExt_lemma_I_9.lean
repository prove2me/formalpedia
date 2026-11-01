-- Prove2me | Theorems.Thm_NeebLieExt_lemma_I_9
-- name    : NeebLieExt.lemma_I_9
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T17:19:24.443552+00:00
-- url     : https://prove2.me/theorems/9a1a55ca-579c-41b2-87a0-a1ae760bf8ec
-- title:
--   Lemma I.9 — the gauge action $\gamma.(S,\omega)$ of $C^1(\mathfrak g,\mathfrak n)$ and its invariants $R_S$, $\widetilde Z^2(\mathfrak g,\mathfrak n)$, $d_S\omega$
-- statement:
--   Throughout, $\mathbb K$ is a topological field of characteristic $0$ (the discrete topology is allowed), topological vector spaces are Hausdorff, and $\mathfrak g$, $\mathfrak n$ are topological Lie algebras over $\mathbb K$.
--
--
--   For $\gamma\in C^1(\mathfrak g,\mathfrak n)$ (continuous linear maps $\mathfrak g\to\mathfrak n$), $S\in C^1_c(\mathfrak g,\operatorname{der}\mathfrak n)$ and $\omega\in C^2(\mathfrak g,\mathfrak n)$ put
--   $$
--   \gamma.(S,\omega):=\Big(S+\operatorname{ad}\circ\gamma,\ \omega+d_S\gamma+\tfrac12[\gamma,\gamma]\Big).
--   $$
--   Then:
--
--   1. This is an action of the abelian group $C^1(\mathfrak g,\mathfrak n)$: $0.(S,\omega)=(S,\omega)$ and $\gamma_1.(\gamma_2.(S,\omega))=(\gamma_1+\gamma_2).(S,\omega)$, and it maps $C^1_c(\mathfrak g,\operatorname{der}\mathfrak n)\times C^2(\mathfrak g,\mathfrak n)$ into itself.
--   2. For every $S$ and $\gamma$,
--   $$
--   R_{S+\operatorname{ad}\circ\gamma}=R_S+\operatorname{ad}\circ\big(d_S\gamma+\tfrac12[\gamma,\gamma]\big).
--   $$
--   3. The set $\widetilde Z^2(\mathfrak g,\mathfrak n):=\{(S,\omega)\in C^1_c(\mathfrak g,\operatorname{der}\mathfrak n)\times C^2(\mathfrak g,\mathfrak n):\ R_S=\operatorname{ad}\circ\omega\}$ is invariant under the action.
--   4. For $(S,\omega)\in\widetilde Z^2(\mathfrak g,\mathfrak n)$, $d_S\omega\in Z^3(\mathfrak g,\mathfrak z(\mathfrak n))_S$: it is a continuous alternating 3-cochain with values in the centre, and $d_S(d_S\omega)=0$.
--   5. On $\widetilde Z^2(\mathfrak g,\mathfrak n)$ the map $(S,\omega)\mapsto d_S\omega$ is constant on orbits: if $(S',\omega')=\gamma.(S,\omega)$ then $d_{S'}\omega'=d_S\omega$.
--
--   The lemma is the computational core of the classification: invariance of $\widetilde Z^2$ and of $d_S\omega$ shows that the set of continuous factor systems is stable under change of section, and $d_S\omega$ is the cocycle whose class is the obstruction to the existence of extensions with a given outer action.
--
--   **Formalization Note** $\tfrac12[\gamma,\gamma](x,y)$ is $[\gamma(x),\gamma(y)]$, and the action is `(gaugeS S γ, gaugeω S ω γ)`.
--
--   Differences from the source:
--   - generalization: the action laws on C¹_c(g, der n) × C²(g, n) → the identities 0.(S, ω) = (S, ω) and γ₁.(γ₂.(S, ω)) = (γ₁ + γ₂).(S, ω) for every linear S : g → der n and every function ω : g → g → n; reason: they are algebraic identities; restricting to C¹_c × C² gives the paper's statement
--   - generalization: (1) for S ∈ C¹_c(g, der n) → (1) for every linear S : g → der n; reason: the identity is algebraic and needs no continuity; it specializes to C¹_c
--   - encoding: (2) invariant subset; (4) constant on orbits → for every γ, γ.(S, ω) ∈ Z̃²(g, n), and d_{S′}ω′ = d_S ω for (S′, ω′) = γ.(S, ω); reason: the orbit of (S, ω) is {γ.(S, ω)}; same statement
--   - encoding: ½[γ, γ] → (x, y) ↦ ⁅γ x, γ y⁆; reason: by the product formula on p. 5, [γ, γ](x, y) = [γx, γy] − [γy, γx] = 2[γx, γy]; same cochain
--   - encoding: cochain spaces C^p(g, V) and C¹_c(g, der n) → functions with the predicates IsCochain2/IsCochain3 (multilinear, alternating, jointly continuous) and linear S : g → LieDerivation K n n with (x, m) ↦ S(x)m jointly continuous; reason: the same sets; joint continuity makes each S(x) a continuous derivation
-- source:
--   Neeb, Non-abelian extensions of topological Lie algebras, arXiv:math/0411256v1, Lemma I.9, p. 8

import Mathlib
import Definitions.Def_NeebLieExt_IsTopLieAlgebra
import Definitions.Def_NeebLieExt_IsCochain2
import Definitions.Def_NeebLieExt_IsContDerAction
import Definitions.Def_NeebLieExt_curv
import Definitions.Def_NeebLieExt_dS1
import Definitions.Def_NeebLieExt_gaugeS
import Definitions.Def_NeebLieExt_InZ2Center

universe u v

namespace NeebLieExt

/-- **Lemma I.9 (the gauge action of `C¹(g, n)` and its invariants).** Neeb, *Non-abelian
extensions of topological Lie algebras*, arXiv:math/0411256v1, Lemma I.9, p. 8: "For topological
Lie algebras g and n the prescription γ.(S, ω) := (S + ad ∘ γ, ω + d_S γ + ½[γ, γ]) defines an
action of the abelian group C¹(g, n) on C¹_c(g, der n) × C²(g, n) with the following properties:
(1) R_{S+ad∘γ} = R_S + ad ∘ (d_S γ + ½[γ, γ]) for S ∈ C¹_c(g, der n) and γ ∈ C¹(g, n).
(2) Z̃²(g, n) := {(S, ω) ∈ C¹_c(g, der n) × C²(g, n): R_S = ad ∘ ω} is an invariant subset.
(3) For (S, ω) ∈ Z̃²(g, n) we have d_S ω ∈ Z³(g, z(n))_S. (4) The map Z̃²(g, n) → Z³(g, z(n)),
(S, ω) ↦ d_S ω is constant on orbits of C¹(g, n)."

The conclusion is the conjunction of: the action laws (`0` acts trivially, `γ₁.(γ₂.(S, ω)) =
(γ₁ + γ₂).(S, ω)`), stability of `C¹_c(g, der n) × C²(g, n)`, and items (1)–(4).

**Formalization Note** `γ.(S, ω) = (gaugeS S γ, gaugeω S ω γ)`; `½[γ, γ](x, y) = ⁅γ x, γ y⁆`.
The action laws and item (1) are stated for every linear `S : g → der n` and every function `ω`
(they are algebraic identities), which specializes to the paper's `C¹_c(g, der n) × C²(g, n)`.
Item (4) says `d_{S'} ω' = d_S ω` for `(S', ω') = γ.(S, ω)`. -/
theorem lemma_I_9 {K : Type*} [Field K] [TopologicalSpace K] [IsTopologicalDivisionRing K] [CharZero K] {n : Type u} [LieRing n] [LieAlgebra K n] [TopologicalSpace n] [IsTopologicalAddGroup n] [ContinuousSMul K n] [T2Space n] [IsTopLieAlgebra n] {g : Type v} [LieRing g] [LieAlgebra K g] [TopologicalSpace g] [IsTopologicalAddGroup g] [ContinuousSMul K g] [T2Space g] [IsTopLieAlgebra g] :
    (∀ (S : g →ₗ[K] LieDerivation K n n) (ω : g → g → n),
        gaugeS S 0 = S ∧ gaugeω S ω 0 = ω) ∧
    (∀ (S : g →ₗ[K] LieDerivation K n n) (ω : g → g → n) (γ₁ γ₂ : g →L[K] n),
        gaugeS (gaugeS S γ₂) γ₁ = gaugeS S (γ₁ + γ₂) ∧
          gaugeω (gaugeS S γ₂) (gaugeω S ω γ₂) γ₁ = gaugeω S ω (γ₁ + γ₂)) ∧
    (∀ (S : g →ₗ[K] LieDerivation K n n) (ω : g → g → n) (γ : g →L[K] n),
        IsContDerAction S → IsCochain2 K ω →
          IsContDerAction (gaugeS S γ) ∧ IsCochain2 K (gaugeω S ω γ)) ∧
    (∀ (S : g →ₗ[K] LieDerivation K n n) (γ : g →L[K] n) (x y : g) (m : n),
        curv (gaugeS S γ) x y m = curv S x y m + ⁅dS1 S γ x y + ⁅γ x, γ y⁆, m⁆) ∧
    (∀ (S : g →ₗ[K] LieDerivation K n n) (ω : g → g → n) (γ : g →L[K] n),
        IsContDerAction S ∧ IsCochain2 K ω ∧ CurvEqAd S ω →
          IsContDerAction (gaugeS S γ) ∧ IsCochain2 K (gaugeω S ω γ) ∧
            CurvEqAd (gaugeS S γ) (gaugeω S ω γ)) ∧
    (∀ (S : g →ₗ[K] LieDerivation K n n) (ω : g → g → n),
        IsContDerAction S → IsCochain2 K ω → CurvEqAd S ω → InZ3Center S (dS2 S ω)) ∧
    (∀ (S : g →ₗ[K] LieDerivation K n n) (ω : g → g → n) (γ : g →L[K] n),
        IsContDerAction S → IsCochain2 K ω → CurvEqAd S ω →
          dS2 (gaugeS S γ) (gaugeω S ω γ) = dS2 S ω) := by sorry

end NeebLieExt
