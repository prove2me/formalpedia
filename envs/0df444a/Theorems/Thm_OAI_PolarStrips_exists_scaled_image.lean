-- Prove2me | Theorems.Thm_OAI_PolarStrips_exists_scaled_image
-- name    : OAI.PolarStrips.exists_scaled_image
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-18T19:31:03.12898+00:00
-- url     : https://prove2.me/theorems/fb27d189-b160-4468-ac70-f5fcedb73a29
-- title:
--   For an injective family of strip functionals, the phase map for a suitable power k lands in the interior of the strip body and of a scaled copy of its polar (OpenAI symmetric polar products)
-- statement:
--   Notation, following OpenAI's definitions. For a finite type $\iota$, $R_\iota = \mathbb R^\iota$ and $C_\iota = \mathbb C^\iota$ (`EuclideanSpace ℝ ι`, `EuclideanSpace ℂ ι`), with real and imaginary parts `re`, `im` $: C_\iota \to R_\iota$. For $b \in R_\iota$, `functional b` is the complex-linear map $z \mapsto \sum_i b_i z_i$. `PlanarLens.F` is OpenAI's lens map, $w \mapsto (8/\pi^2) \sum_n \texttt{term}\ n\ w$; `PlanarLens.D` $= F(\text{open unit disc})$ is the lens, and `PlanarLens.g` is the inverse of $F$ on the unit disc (Mathlib's `Function.invFunOn`). For a family $\ell = (\ell_j)_{j \in \kappa}$ of complex functionals, `PolarStrips.domain ℓ` $= \{z : \ell_j(z) \in D \text{ for all } j\}$ and `PolarStrips.tuple ℓ k z` $= \bigl(g(\ell_j(z))^k\bigr)_{j}$. For $b : \kappa \to R_\iota$ and $k \in \mathbb N$,
--   $$\texttt{phase}\ b\ k\ z \;=\; \Bigl(\operatorname{im} z,\ \ -\operatorname{re} z - \sum_j \texttt{PlanarLens.primitive}\ k\ (\texttt{functional}\ (b_j)\ z)\cdot b_j\Bigr) \in R_\iota \times R_\iota,$$
--   where `PlanarLens.primitive k z` $= J\ k\ (\operatorname{Re} z)\ (\operatorname{Im} z)$ is a real-valued function defined by OpenAI. Finally `ConvexPolar.stripBody b` $= \{x \in R_\iota : |\langle b_j, x\rangle| \le 1 \text{ for all } j\}$ and `ConvexPolar.polar K` $= \{p : \langle q, p\rangle \le 1 \text{ for all } q \in K\}$.
--
--   **Statement.** Let $\iota, \kappa$ be finite types, $b : \kappa \to R_\iota$ such that $x \mapsto (\langle b_j, x\rangle)_{j \in \kappa}$ is injective, and $\eta > 0$. Then there is a natural number $k \ge 1$ such that for every $z \in C_\iota$ with $z \in$ `PolarStrips.domain (fun j => functional (b j))` and $\|$`PolarStrips.tuple (fun j => functional (b j)) k z`$\|^2 < 1$:
--   - the first component of `phase b k z` lies in the interior of `ConvexPolar.stripBody b`, and
--   - $\bigl((1+\eta)\,\pi k/4\bigr)^{-1}$ times its second component lies in the interior of `ConvexPolar.polar (ConvexPolar.stripBody b)`.
--
--   Lean: `OAI.PolarStrips.exists_scaled_image`, OpenAI's theorem of that name (in `lean/OAI/Geometry/PolarProducts/MomentumBounds.lean`). All the definitions above come from the definitions bundle `OAIQWSP000` of this split.
-- source:
--   OpenAI, Symplectic Balls in Symmetric Polar Products, OpenAI Math Release, September 22, 2026, https://github.com/openai/math (result family 087; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Symplectic-Balls-in-Symmetric-Polar-Products-September-22-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/PolarProducts/MomentumBounds.lean (declaration OAI.PolarStrips.exists_scaled_image)

import Mathlib
import Definitions.Def_OAIQWSP000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u70 u71 u72 u73

section LowerBoundInline
open Set Filter Function
open scoped Topology ContDiff NNReal
open Set Filter Metric
open scoped Topology ContDiff
open Set Filter Function MeasureTheory Metric
open scoped Topology ContDiff NNReal
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff NNReal
open Set Filter
open scoped Topology ContDiff
open Set Filter Function
open scoped Topology ContDiff
open Set Filter Function
open scoped ContDiff Topology
open Set MeasureTheory
open scoped ContDiff Interval Topology
open Set
open scoped Topology ContDiff
open Set
open Set MeasureTheory
open scoped ContDiff Interval Topology
open Set Filter Complex
open scoped Topology ContDiff
open MeasureTheory intervalIntegral Set
open scoped Real

namespace PolarStrips
open Set Filter ComplexCoordinates
open scoped Topology ContDiff
noncomputable section
variable {ι : Type u70} {κ : Type u71} [Fintype ι] [Fintype κ]

theorem exists_scaled_image (b : κ → R ι)
    (hb : Function.Injective (fun x : R ι => fun j => inner (𝕜 := ℝ) (b j) x))
    {η : ℝ} (hη : 0 < η) :
    ∃ k : ℕ, 1 ≤ k ∧ ∀ z : C ι,
      z ∈ domain (fun j => functional (b j)) → ‖tuple (fun j => functional (b j)) k z‖^2 < 1 →
      (phase b k z).1 ∈ interior (ConvexPolar.stripBody b) ∧
        (((1+η)*Real.pi*(k : ℝ)/4)⁻¹ • (phase b k z).2) ∈ interior (ConvexPolar.polar (ConvexPolar.stripBody b)) := by
  sorry

end
end PolarStrips

open Set
open scoped ContDiff ENNReal

end LowerBoundInline

end OAI
end
