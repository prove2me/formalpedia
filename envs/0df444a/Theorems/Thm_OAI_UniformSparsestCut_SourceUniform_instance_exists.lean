-- Prove2me | Theorems.Thm_OAI_UniformSparsestCut_SourceUniform_instance_exists
-- name    : OAI.UniformSparsestCut.SourceUniform.instance_exists
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-19T01:48:19.638989+00:00
-- url     : https://prove2.me/theorems/ae041db3-4834-48ec-b64d-f1bc1872b64d
-- title:
--   A pivot family on m + 1 ≥ 3000 points yields a uniform sparsest cut instance with OPT ≥ 1 and small Goemans–Linial value (OpenAI uniform sparsest cut)
-- statement:
--   **Objects** (definitions bundle `OAIQWUS000` of this split, and the published bundle `Def_UniformSparsestCut`). `Capacity n` is a nonnegative symmetric capacity on `Fin n` with zero diagonal; `OPT C` is its uniform sparsest cut value and `glValue C` its Goemans–Linial semidefinite value, as in the published goal `OAI.UniformSparsestCut.mainGap`. `PivotFamily.PFamily d` is OpenAI's structure of pivot direction families in dimension $d$. `KernelApprox.cstar` $= 2\int_0^\infty \mathrm{profile}(t)\,dt$, `SourceMetric.C₀` $= 9 + 2\,\mathrm{cstar}$, `SourceContraction.H` $= \int |\rho'(t)|\,dt$ for OpenAI's mollifier $\rho$ (`ProductMollifier.rho`), `SourceWeighted.D` $= 4\,\mathrm{cstar} + \mathrm{C₀}$, `SourceContraction.C` $= 2(\mathrm{cstar} + \mathrm{C₀}) + \pi(1100000000 + \mathrm{C₀}\cdot H) + 1$, and `SourceContraction.weight d` $= \sqrt d\,(\log d)^2\sqrt{\log d}$.
--
--   **Statement.** Let $m \in \mathbb N$, $d = m + 1$, and let $f$ be a pivot family in dimension $d$ (`PivotFamily.PFamily (m+1)`). Suppose $3000 \le d$, $1 \le \log d$, $H \le d$, $4D \le d$ and $\mathrm{C₀} + 1 \le (\mathrm{cstar}/6)\,d$. Then there are $n \in \mathbb N$ and a capacity $C$ on $n$ points with
--   $$d^{\,d} \le n \le d^{\,4030 d},\qquad 2 \le n,\qquad 1 \le \mathrm{OPT}(C),\qquad 0 < \mathrm{glValue}(C) \le \frac{(\mathrm{C} + 1)\,\mathrm{weight}(d)}{(\mathrm{cstar}/6)\,d}.$$
--
--   Lean: `OAI.UniformSparsestCut.SourceUniform.instance_exists`, OpenAI's lemma of that name (in `lean/OAI/Combinatorics/SparsestCut/UniformMetric.lean`).
-- source:
--   OpenAI, Near-square-root logarithmic integrality gaps for uniform sparsest cut, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 117; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Combinatorics/SparsestCut/UniformMetric.lean (declaration OAI.UniformSparsestCut.SourceUniform.instance_exists)

import Mathlib
import Definitions.Def_UniformSparsestCut
import Definitions.Def_OAIQWUS000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open scoped BigOperators Topology NNReal RealInnerProductSpace InnerProductSpace Matrix ContDiff ENNReal
open MeasureTheory ProbabilityTheory Set Filter Matrix

noncomputable section

namespace UniformSparsestCut.SourceUniform
open scoped BigOperators
open SourceMetric SourceParameters
noncomputable section

lemma instance_exists {m : ℕ} (f : PivotFamily.PFamily (m+1))
    (hm : 3000 ≤ m+1) (hl : 1≤Real.log (m+1:ℕ)) (hH : SourceContraction.H≤(m+1:ℕ))
    (hD : 4*SourceWeighted.D≤(m+1:ℕ))
    (ha : C₀+1≤KernelApprox.cstar/6*(m+1:ℕ)) :
    ∃ (n : ℕ) (C : Capacity n), (m+1)^(m+1)≤n ∧ n≤(m+1)^(4030*(m+1)) ∧
      2≤n ∧ 1≤OPT C ∧ 0<glValue C ∧
      glValue C≤(SourceContraction.C+1)*SourceContraction.weight (m+1)/
        (KernelApprox.cstar/6*(m+1:ℕ)) := by
  sorry
end
end UniformSparsestCut.SourceUniform

end

end OAI
end
