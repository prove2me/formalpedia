-- Prove2me | Theorems.Thm_OAI_BassTrace_Sparse_GraphGeometry_global_zero_ball_mass_bound
-- name    : OAI.BassTrace.Sparse.GraphGeometry.global_zero_ball_mass_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-23T21:18:16.674186+00:00
-- url     : https://prove2.me/theorems/905616dc-ad52-4437-b5f7-e866cca6fe45
-- title:
--   Near-minimal separating filtrations have zero-stratum ball mass O(ε) (OpenAI Bass trace, Section 5)
-- statement:
--   **Setting** (definitions bundle `OAIQWBAS002` of this split and the bundles it imports). A countable group $H$ acts freely (`IsCancelSMul`) on a countable vertex set $Y$, by automorphisms of a connected, locally finite simple graph $\Gamma$ on $Y$ that are isometries of its graph metric (`graphMetric`). $K$ is a simplicial complex on $Y$ whose faces are permuted by $H$, with finitely many $H$-orbits of $n$-simplices ($n > 0$). Every face of $K$ lies in an $n$-simplex of $K$ whose vertices span a connected subgraph of $\Gamma$. The parameter space $X$ is a compact, Hausdorff, totally disconnected Borel space with a free continuous $H$-action, and $\mu$ is a finite $H$-invariant measure on $X$.
--
--   The realization of $K$ consists of finitely supported probability vectors on $Y$ (`FinProbability`). It carries the distance `realizationDistance`: the transport distance for the graph metric, divided by $\sqrt n$. An $n$-stage separating filtration $Q$ (`OrbitForms.SeparatingFiltration`) assigns to each parameter $x \in X$, equivariantly, a chain of subdivisions of $K$ with nested marked subcomplexes $Z_n(x) = |K| \supseteq \dots \supseteq Z_0(x)$. Each stage drops dimension (`Cuts.DimensionDrop`: a face of the finer subdivision lying in $Z_i(x)$ has fewer vertices than the face of $Z_{i+1}(x)$ containing it), and every preconnected subset of $Z_{i+1}(x) \setminus Z_i(x)$ has diameter at most $R$. $Q$ is $\varepsilon$-near-minimal (`NearMinimal`) when no admissible equivariant replacement of any stage lowers its normalized area (`normalizedArea`, the $\mu$-integrated simplexwise area summed over orbit representatives of top simplices) by more than $\varepsilon$. For a probability vector $c$ and a radius $r$, the ball mass `ballMass … (Q.pair 0) μ univ 0 c r` is the $\mu$-integral of the number of points of the zero stratum $Z_0(x)$ within distance $r$ of $c$, counted simplexwise over the top simplices.
--
--   **The statement.** Assume moreover that every vertex of $\Gamma$ has at most $D \ge 2$ neighbours. Let $R > 0$ and $0 \le r \le R$ satisfy the volume margin
--   $$\texttt{ballVolumeBound}\ D\ n\ R \;<\; \frac{(R - r)^n}{n!},$$
--   and let $c$ be a finitely supported probability vector on $Y$ with at most $n + 1$ points in its support. Then there is a constant $C \ge 0$ such that, for every $\varepsilon \ge 0$ and every $\varepsilon$-near-minimal $n$-stage separating filtration $Q$ of diameter $R$,
--   $$\texttt{ballMass}\ (Q.\mathrm{pair}\ 0)\ \mu\ X\ 0\ c\ r \;\le\; C\,\varepsilon .$$
--
--   This is the local estimate behind the paper's Proposition 5.1 (Section 5): near minimizers leave very few points in the final zero-dimensional stratum.
--
--   Lean: `OAI.BassTrace.Sparse.GraphGeometry.global_zero_ball_mass_bound`, OpenAI's theorem of that name (in `lean/OAI/RingTheory/BassTrace/BallMass.lean`).
-- source:
--   OpenAI, The Bass trace conjecture and the characteristic-zero Kaplansky idempotent conjecture, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 207; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Bass-trace-conjecture-for-complex-group-rings-September-24-2026/The-Bass-trace-conjecture-for-complex-group-rings-September-24-2026.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/RingTheory/BassTrace/BallMass.lean (declaration OAI.BassTrace.Sparse.GraphGeometry.global_zero_ball_mass_bound)

import Mathlib
import Definitions.Def_OAIQWBAS002

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace BassTrace

open Set MeasureTheory
open Finset MeasureTheory intervalIntegral

namespace Sparse.GraphGeometry

section

open Set Finset MeasureTheory

open scoped BassTrace.Sparse Classical ENNReal

variable {H Y X : Type*} [Group H] [MulAction H Y] [DecidableEq Y] [Countable Y]
  [Countable H] [IsCancelSMul H Y]
  [TopologicalSpace X] [T2Space X] [CompactSpace X] [TotallyDisconnectedSpace X]
  [MulAction H X] [ContinuousConstSMul H X] [IsCancelSMul H X]
  [MeasurableSpace X] [BorelSpace X]

variable {K : PreAbstractSimplicialComplex Y} {n : ℕ}

variable [hact : Fact (∀ (h : H) s,s∈K.faces → s.map (MulAction.toPerm h).toEmbedding∈K.faces)]

attribute [local instance] OAI.BassTrace.Sparse.GraphGeometry.instMulActionSourceTop_4
local instance instCountableSourceTop_4_rc0e15c_1 : Countable (SourceTop K n) := inferInstanceAs (Countable {s : Finset Y // s∈K.faces ∧ s.card=n+1})
variable [Finite (MulAction.orbitRel.Quotient H (SourceTop K n))]

variable (Γ : SimpleGraph Y) [Γ.LocallyFinite] (hΓ : Γ.Connected)

variable (hΓaut : ∀ (h : H) u v,Γ.Adj (h•u) (h•v) ↔ Γ.Adj u v)

variable (hi : ∀ h : H,@Isometry Y Y (graphMetric Γ hΓ).toPseudoEMetricSpace
  (graphMetric Γ hΓ).toPseudoEMetricSpace (fun y=>h•y))

variable (hn : 0<n)

variable (hK : ∀ s∈K.faces,∃ σ∈K.faces,s⊆σ ∧ σ.card=n+1 ∧
  (Γ.induce (σ : Set Y)).Connected)

include hi hn hK hΓaut in

theorem global_zero_ball_mass_bound (μ : Measure X) [IsFiniteMeasure μ]
    (hμ : ∀ h : H,MeasurePreserving (fun x : X=>h•x) μ μ)
    {R : ℝ} (hR : 0<R) (c : FinProbability Y) (hc : c.coeff.support.card≤n+1)
    (r : ℝ) (hr : 0≤r) (hrR : r≤R)
    (D : ℕ) (hD : 2≤D) (hdeg : ∀ v,Fintype.card (Γ.neighborSet v)≤D)
    (hmargin : ballVolumeBound D n R<dividedPower n (R-r)) :
    ∃ C : ℝ,0≤C ∧ ∀ (ε : ℝ),0≤ε →
      ∀ Q : OrbitForms.SeparatingFiltration (H := H) (X := X)
        (Geometry.SimplicialComplex.onFinsupp (𝕜 := ℝ) K)
        (realizationDistance Γ hΓ K n) R n,
      Q.NearMinimal (realizationDistance Γ hΓ K n) R
        (fun d P=>(normalizedArea Γ μ (OrbitAreas.orbitReps (H := H) (T := SourceTop K n)) P d).toReal) ε →
      (ballMass (n := n) Γ hΓ (Q.pair 0) μ univ 0 c r).toReal≤C*ε := by
  sorry

end

end Sparse.GraphGeometry

end BassTrace

end

end OAI
end
