-- Prove2me | Theorems.Thm_OAI_BassTrace_Sparse_vanishing_of_zero_strata
-- name    : OAI.BassTrace.Sparse.vanishing_of_zero_strata
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-23T21:16:30.123341+00:00
-- url     : https://prove2.me/theorems/6b13dbae-4629-477c-86ed-d15a85d0ff30
-- title:
--   Separating filtrations with small zero strata force invariant cocycles to vanish on coinvariant cycles (OpenAI Bass trace, Section 6)
-- statement:
--   **Setting** (definitions bundle `OAIQWBAS002` of this split and the bundles it imports). A group $H$ acts on a linearly ordered vertex set $Y$ and on a compact measurable space $X$, and $\mu$ is an $H$-invariant probability measure on $X$. $\Gamma$ is a connected, locally finite simple graph on $Y$, and $K$ is a simplicial complex on $Y$ in which every face lies in an $n$-simplex ($n > 0$) whose vertices span a connected subgraph of $\Gamma$. `augmentedComplex K` is $K$ with the empty face added. Its chains in degree $k$ are the elements of the $k$-th exterior power $\Lambda^k \mathbb C^{(Y)}$ (`Degree Y k`) spanned by wedges of vertices of faces. The differential `d` is contraction with the augmentation, $\partial(\delta_{y_0} \wedge \dots \wedge \delta_{y_j}) = \sum_i (-1)^i \delta_{y_0} \wedge \dots \widehat{\delta_{y_i}} \dots \wedge \delta_{y_j}$. For an $H$-invariant complex, `relations` in degree $k$ is the span of the differences $h\cdot a - a$ of chains, so a chain whose boundary lies in it is a cycle in the coinvariants. Separating filtrations (`OrbitForms.SeparatingFiltration`) for the distance `realizationDistance` are as in the companion statement `OAI.BassTrace.Sparse.GraphGeometry.global_zero_ball_mass_bound`; $Z_0(x)$ is the zero stratum `(Q.pair 0).P` at the parameter $x$.
--
--   **The statement.** Let $R \ge 0$, let `augmentedComplex K` be $H$-invariant, and let $C(\sigma) \ge 0$ for each $n$-simplex $\sigma$ of $K$. Suppose that for every $\varepsilon > 0$ there is an $n$-stage separating filtration $Q$ of diameter $R$ with
--   $$\int_X \#\bigl(Z_0(x) \cap |\sigma|\bigr)\,d\mu(x) \;\le\; C(\sigma)\,\varepsilon \quad\text{for every } n\text{-simplex } \sigma,$$
--   where $|\sigma|$ is the convex hull of the vertices of $\sigma$. Let $\psi : \Lambda^{n+1}\mathbb C^{(Y)} \to \mathbb C$ be a complex-linear functional that is $H$-invariant ($\psi(h \cdot c) = \psi(c)$) and a cocycle ($\psi(\partial c) = 0$ for every $c$ in degree $n+2$). Then $\psi(c) = 0$ for every chain $c$ of `augmentedComplex K` in degree $n + 1$ whose boundary lies in the relations of degree $n$.
--
--   This is the deduction, in the paper's Section 6, of the sparse-chain vanishing Theorem 2.1 from the zero-stratum bound of Proposition 5.1. The filtrations give equivariant chain maps homotopic to the inclusion, and their cocycle evaluations tend to zero.
--
--   Lean: `OAI.BassTrace.Sparse.vanishing_of_zero_strata`, OpenAI's lemma of that name (in `lean/OAI/RingTheory/BassTrace/SparseBounds.lean`).
-- source:
--   OpenAI, The Bass trace conjecture and the characteristic-zero Kaplansky idempotent conjecture, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 207; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Bass-trace-conjecture-for-complex-group-rings-September-24-2026/The-Bass-trace-conjecture-for-complex-group-rings-September-24-2026.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/RingTheory/BassTrace/SparseBounds.lean (declaration OAI.BassTrace.Sparse.vanishing_of_zero_strata)

import Mathlib
import Definitions.Def_OAIQWBAS002

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set MeasureTheory
open Finset MeasureTheory intervalIntegral
noncomputable section

namespace BassTrace.Sparse

open Set Finset MeasureTheory

open scoped BassTrace.Sparse Classical

open Oriented ChainHomotopy Fundamental BarycentricChains SubdivisionChains GraphGeometry

variable {H Y X : Type*} [Group H] [MulAction H Y] [LinearOrder Y]
  [LinearOrder (Y →₀ ℝ)] [TopologicalSpace X] [MulAction H X]
  [CompactSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]

variable {K : PreAbstractSimplicialComplex Y} {n : ℕ} {R : ℝ}

variable (Γ : SimpleGraph Y) [Γ.LocallyFinite] (hΓ : Γ.Connected)

variable (hK : ∀ s∈K.faces,∃ σ∈K.faces,s⊆σ ∧ σ.card=n+1 ∧
  (Γ.induce (σ : Set Y)).Connected)

variable (hn : 0<n) (hR : 0≤R) (y₀ : Y)

variable (μ : Measure X) [IsProbabilityMeasure μ]

attribute [local instance] OAI.BassTrace.Sparse.instMeasurableSpaceFinsuppReal_solutions_3
local instance instBorelSpaceFinsuppReal_solutions_3_r5c79b7_1 : BorelSpace (Y →₀ ℝ) := ⟨rfl⟩
include hK hn hR y₀ in
lemma vanishing_of_zero_strata
    (hInv : (augmentedComplex K).IsInvariant (H := H))
    (hμ : ∀h : H,MeasurePreserving (fun x : X=>h • x) μ μ)
    (C : SourceTop K n → ℝ) (hC : ∀σ,0≤C σ)
    (hzero : ∀ε : ℝ,0<ε → ∃Q : OrbitForms.SeparatingFiltration (H := H) (X := X)
      (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K)
      (realizationDistance Γ hΓ K n) R n,
      ∀σ : SourceTop K n,(∫x,(Measure.count ((Q.pair 0).P.val x∩
        convexHull ℝ (simplexVertices σ.val : Set (Y →₀ ℝ)))).toReal ∂μ)≤C σ*ε)
    (ψ : Degree Y (n+1) →ₗ[ℂ] ℂ)
    (hψ : ∀(h : H) c,ψ (relabel (n+1) (fun y=>h • y) c)=ψ c)
    (hψd : ∀c,ψ (d (n+1) c)=0)
    (c : (augmentedComplex K).chains (n+1))
    (hc : (⟨d n c,(augmentedComplex K).d_mem n c.property⟩ :
      (augmentedComplex K).chains n)∈(augmentedComplex K).relations hInv n) : ψ c=0 := by
  sorry

end BassTrace.Sparse

end

end OAI
end
