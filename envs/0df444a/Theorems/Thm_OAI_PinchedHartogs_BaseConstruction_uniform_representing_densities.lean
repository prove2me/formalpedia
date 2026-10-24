-- Prove2me | Theorems.Thm_OAI_PinchedHartogs_BaseConstruction_uniform_representing_densities
-- name    : OAI.PinchedHartogs.BaseConstruction.uniform_representing_densities
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-23T16:06:02.492975+00:00
-- url     : https://prove2.me/theorems/3921e99e-beff-45d7-b229-a2b34b1926fe
-- title:
--   Uniform representing densities on the unit sphere of C² (OpenAI pinched Kähler threefold, Theorem 4.2)
-- statement:
--   `Base` ($\mathbb C^2$) is from the published bundle `Def_PinchedKahler`; the other definitions are from the definitions bundle `OAIQWPH001` of this split, following Sections 3–4 of the paper:
--   - `Sphere` is the unit sphere $\mathbb S^3 \subset \mathbb C^2$; `ProjectivelySeparated ρ P` says the points of the finite set $P$ are pairwise at projective distance $\sqrt{1 - |\langle\xi, p\rangle|^2} \ge \rho$;
--   - `RadialProfiles a` bundles the fixed radial profiles $f, b$ and constants $s, F, R, \ldots$ of Lemma 3.4 (with their smoothness, plateau, cancellation, ODE and negativity conditions);
--   - `density Q R f b P j` is the density $W_j$ of the recursion (4.2): $W_0 = 1$ and $W_{j+1} = W_j + \sum_{p \in P(Q^{j+1})}$ (a correction supported near $p$ at scale $Q^{-(j+1)}$);
--   - `DensityStage W Q c K j` collects the stage estimates: $W_j > 0$ on the sphere, horizontal derivative bound $K\sqrt{Q^j}\,W_j$, phase derivative bound $KQ^j W_j$, and $cW_{j-1} \le W_j \le 2W_{j-1}$;
--   - `PhaseBandwidth W ℓ`: along each phase circle $z \mapsto zp$, $W$ is a trigonometric polynomial with frequencies in $[-\ell, \ell]$; `densityBandwidth Q j` $= \sum_{i<j} Q^{i+1}$;
--   - `OrbitMeanOne W`: the mean of $W$ over each phase circle is $1$;
--   - `densityMeasure W` is $W\,d\sigma$ for the normalized surface measure $\sigma$; `Represents μ`: $\int p\,d\mu = p(0)$ for every polynomial $p$ on $\mathbb C^2$ (holomorphic evaluation at $0$).
--
--   **Statement.** For every `RadialProfiles a` there are $c, K > 0$ such that for every $D > 2\sqrt{2R}$ and every $k_{\min}$ there is $Q_0$ such that every $Q \ge Q_0$ has $Q \ge 2$, $Q \ge k_{\min}$, and, for every family of finite sets $P(Q^{j+1})$ that are `ProjectivelySeparated` at scale $D/\sqrt{Q^{j+1}}$, every stage $W_j$ is smooth, satisfies `DensityStage … c K j`, `PhaseBandwidth` with bandwidth `densityBandwidth Q j` and `OrbitMeanOne`, and $W_j\,d\sigma$ is a probability measure that represents evaluation at $0$.
--
--   This is Theorem 4.2 of the paper.
--
--   Lean: `OAI.PinchedHartogs.BaseConstruction.uniform_representing_densities`, OpenAI's theorem of that name (in `lean/OAI/Geometry/Kahler/BaseDensityTheorem.lean`). It is published as an intermediate statement of this split because the single-file proof takes longer than the platform's verifier allows.
-- source:
--   OpenAI, A negatively pinched Kähler threefold without bounded holomorphic coordinates, OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 359; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-negatively-pinched-Kahler-threefold-without-bounded-holomorphic-coordinates-September-25-2026/paper.pdf, Theorem 4.2; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/Kahler/BaseDensityTheorem.lean (declaration OAI.PinchedHartogs.BaseConstruction.uniform_representing_densities)

import Mathlib
import Definitions.Def_PinchedKahler
import Definitions.Def_OAIQWPH001

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Complex
open scoped ContDiff Matrix Matrix.Norms.Elementwise
open scoped ContDiff Matrix Matrix.Norms.Elementwise ComplexOrder
open scoped ContDiff ComplexOrder
open scoped ContDiff ENNReal
open Set Filter Topology MeasureTheory
open scoped ContDiff ENNReal Pointwise
open scoped ContDiff
open Set Filter Topology
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ContDiff
namespace PinchedHartogs.BaseConstruction

theorem uniform_representing_densities {a : ℝ} (p : RadialProfiles a) :
    ∃ c K : ℝ, 0 < c ∧ 0 < K ∧ ∀ D : ℝ, 2*Real.sqrt (2*p.R) < D →
    ∀ kmin : ℕ, ∃ Q₀ : ℕ, ∀ Q : ℕ, Q₀ ≤ Q →
    2 ≤ Q ∧ kmin ≤ Q ∧ ∀ P : ℕ → Finset Sphere,
      (∀ j, ProjectivelySeparated (D/Real.sqrt (Q^(j+1):ℕ)) (P (Q^(j+1)))) →
      ∀ j, ContDiff ℝ ∞ (density Q p.R p.f p.b P j) ∧
        DensityStage (density Q p.R p.f p.b P) Q c K j ∧
        PhaseBandwidth (density Q p.R p.f p.b P j) (densityBandwidth Q j) ∧
        OrbitMeanOne (density Q p.R p.f p.b P j) ∧
        IsProbabilityMeasure (densityMeasure (density Q p.R p.f p.b P j)) ∧
        Represents (densityMeasure (density Q p.R p.f p.b P j)) := by
  sorry

end PinchedHartogs.BaseConstruction

end

end OAI
end
