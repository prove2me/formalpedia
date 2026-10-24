-- Prove2me | Theorems.Thm_OAI_CommonPrices_physical_joint_price
-- name    : OAI.CommonPrices.physical_joint_price
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-23T21:39:47.968309+00:00
-- url     : https://prove2.me/theorems/73385889-4754-492b-9c70-a3d72162287d
-- title:
--   Cell-wise price bound for gradients and oscillations of disk averages at one scale (OpenAI centered disk maximal operator, Section 3)
-- statement:
--   **Notation** (definitions bundle `OAIQWCDE000` of this split). $A_t g(x)$ is the disk average `signedAverage g x t` (see `OAI.SobolevBand.smooth_dyadic_bound`). For $r > 0$ and $k \in \mathbb N$, `scale r k` is $r_k = 2^k r$. `point r p` is the lattice point $r p \in \mathbb C$ for $p \in \mathbb Z^2$, and `cell (point r_k p) r_k` is the half-open square of side $r_k$ with lower-left corner $r_k p$.
--   - **Grid data.** `Grid N` is the box $\{-N, \dots, N\}^2$ of lattice indices. `cellRoots N p` is the set of indices of `Grid N` within $\ell^\infty$ distance $20$ of $p$.
--   - **Masses and prices.** For $h = \nabla g$, `rootMass h r k S` sums over $q \in S$ the norm of the tent-weighted mass of $h$ near $r_k q$ (`scalarMass`). `cellPrice N r h k S` sums over $q \in S$ the discounted price `rootPrice N r h k q` of the paper's Proposition 3.3. That price is built from the scalar coordinates of $h$ along the directions of a fixed finite palette (`fixedPalette`), at scale $k$ and all finer levels.
--   - **Radii.** A radius $t$ is a physical endpoint radius at scale $r_k$ for $g$ at $y$ (`PhysicalEndpointRadius g r_k y t`) when $t \in [r_k, 2r_k]$, and either $t$ is an endpoint of that interval or $A_t g(y)$ is maximal over it.
--
--   **The statement.** There is an absolute constant $C > 0$ with the following property. Let $r > 0$, $R \ge 0$ and $N$ with $R/r + 1 \le N$. Let $g : \mathbb C \to \mathbb R$ be $C^1$ with integrable gradient, with $\nabla g = 0$ outside the closed disk of radius $R$, and with bounded derivative. Then for every $k \in \mathbb N$, every $p \in \mathbb Z^2$ and every palette label $n$ there is a measurable $F : \mathbb C \to [0, \infty]$ such that, with $Q$ = `cell (point r_k p) r_k`:
--   - $\int_Q F \le C\,\bigl(\texttt{rootMass} + \texttt{cellPrice}\bigr)$, both taken for $h = \nabla g$, scale $k$ and the roots `cellRoots N p`;
--   - for $y \in Q$ and every physical endpoint radius $t$ at scale $r_k$, $\lVert\nabla_y A_t g(y)\rVert \le F(y)$;
--   - for $y \in Q$ and all $0 < t, t' \le 4r_k$, $\lvert A_t g(y) - A_{t'} g(y)\rvert / r_k \le F(y)$.
--
--   This is the Lean form of the cell estimate in the paper's Proposition 3.3 (common discounted prices): one integrable majorant on each pricing cell pays both the gradients of the averages at selected radii and their oscillation over $(0, 4r_k]$.
--
--   Lean: `OAI.CommonPrices.physical_joint_price`, OpenAI's theorem of that name (in `lean/OAI/Analysis/DiskMaximal/BandBounds.lean`).
-- source:
--   OpenAI, An Endpoint Gradient Bound for the Centered Disk Maximal Operator, OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 085; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/An-Endpoint-Gradient-Bound-for-the-Centered-Disk-Maximal-Operator-September-26-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/DiskMaximal/BandBounds.lean (declaration OAI.CommonPrices.physical_joint_price)

import Mathlib
import Definitions.Def_OAIQWCDE000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory Set
open scoped ENNReal NNReal Topology ContDiff
open scoped RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology ENNReal
open scoped Real RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology RealInnerProductSpace ContDiff
open MeasureTheory Set Filter
open scoped Topology Interval NNReal
open MeasureTheory Set Filter
open scoped Topology NNReal Real
open MeasureTheory Set Metric
open scoped ENNReal NNReal Topology
open MeasureTheory Set
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped ENNReal NNReal Topology
open MeasureTheory Set Metric
open scoped ENNReal NNReal
open MeasureTheory Set
open scoped ENNReal NNReal
open Finset
open scoped RealInnerProductSpace
open MeasureTheory Set Metric
open scoped ENNReal NNReal Topology
open MeasureTheory Set
open scoped ENNReal NNReal RealInnerProductSpace
open MeasureTheory Set
open scoped ENNReal NNReal Topology
open MeasureTheory Set Metric
open scoped ENNReal NNReal RealInnerProductSpace
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open scoped ContDiff
open Finset
open MeasureTheory Set Metric Filter
open scoped ENNReal NNReal RealInnerProductSpace ContDiff Topology
open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal NNReal Topology RealInnerProductSpace ContDiff
open MeasureTheory Set Metric Filter Finset
open scoped ENNReal NNReal RealInnerProductSpace ContDiff Topology
open MeasureTheory Set
open scoped RealInnerProductSpace

noncomputable section

namespace CommonPrices
open DyadicHats ConeCoordinates Finset DiskMoments PhysicalCells SignedRuns FiniteLabels ActualLabels

theorem physical_joint_price : ∃ C : ℝ, 0 < C ∧
    ∀ {N : ℕ} {r R : ℝ} (hr : 0 < r) (hR : 0 ≤ R) (hN : R/r+1 ≤ (N:ℝ))
    {g : ℂ → ℝ}, ContDiff ℝ 1 g → Integrable (gradient g) →
    (∀ y, gradient g y ≠ 0 → ‖y‖ ≤ R) →
    (∃ D : ℝ, ∀ y, ‖fderiv ℝ g y‖ ≤ D) → ∀ (k : ℕ) (p : ℤ × ℤ) (n : Label),
    ∃ F : ℂ → ℝ≥0∞, Measurable F ∧
      (∫⁻ y in cell (point (scale r k) p) (scale r k), F y) ≤ ENNReal.ofReal
        (C*(rootMass (gradient g) r k (cellRoots N p)+cellPrice N r (gradient g) k (cellRoots N p))) ∧
      (∀ y ∈ cell (point (scale r k) p) (scale r k), ∀ t,
        PhysicalEndpointRadius g (scale r k) y t →
        ENNReal.ofReal ‖gradient (fun z => signedAverage g z t) y‖ ≤ F y) ∧
      (∀ y ∈ cell (point (scale r k) p) (scale r k), ∀ t t',
        0 < t → t ≤ 4*scale r k → 0 < t' → t' ≤ 4*scale r k →
        ENNReal.ofReal (|signedAverage g y t-signedAverage g y t'|/scale r k) ≤ F y) := by
  sorry
end CommonPrices

end

end OAI
end
