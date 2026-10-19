-- Prove2me | Theorems.Thm_OAI_ClassicalON_ising_edge_covariance_nonneg
-- name    : OAI.ClassicalON.ising_edge_covariance_nonneg
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-19T02:54:12.975123+00:00
-- url     : https://prove2.me/theorems/743f8c06-bb75-4a64-8a48-3e0baf457bee
-- title:
--   Griffiths' second inequality (GKS II) for edge correlations of a ferromagnetic Ising model, by Ginibre's doubling: ⟨σ_eσ_f⟩ ≥ ⟨σ_e⟩⟨σ_f⟩
-- statement:
--   Let $V$ (vertices) and $E$ (edges) be finite types, and let each edge $e$ join the vertices $\mathrm{left}(e)$ and $\mathrm{right}(e)$ (`left right : E → V`; loops and multiple edges are allowed). A configuration is $s : V \to \mathrm{Bool}$, with spin $\sigma_v(s) = 1$ if $s(v)$ is true and $-1$ otherwise (`signValue`), and for an edge $e$ write $\sigma_e = \sigma_{\mathrm{left}(e)}\,\sigma_{\mathrm{right}(e)}$ (`isingEnergy left right e`). Let $b : E \to \mathbb R$ be nonnegative couplings, $b(e) \ge 0$ for all $e$. The Ising mean (`isingMean`, from the definitions bundle of this split) of $f$ is
--   $$\langle f\rangle = \frac{\int f(s)\,e^{H(s)}\,d\rho(s)}{\int e^{H(s)}\,d\rho(s)}, \qquad H(s) = \sum_{e \in E} b(e)\,\sigma_e(s),$$
--   where $\rho$ is the uniform probability measure on $\mathrm{Bool}^V$ (`isingReference`, the product of $\tfrac12$ counting measure). Then for all edges $e, f$,
--   $$\langle \sigma_e\rangle\,\langle \sigma_f\rangle \;\le\; \langle \sigma_e\,\sigma_f\rangle.$$
--
--   Lean: `OAI.ClassicalON.ising_edge_covariance_nonneg`.
-- source:
--   Classical (R. B. Griffiths, Correlations in Ising ferromagnets. II, J. Math. Phys. 8 (1967), 484–489; D. G. Kelly and S. Sherman, General Griffiths' inequalities on correlations in Ising ferromagnets, J. Math. Phys. 9 (1968), 466–484; J. Ginibre, General formulation of Griffiths' inequalities, Comm. Math. Phys. 16 (1970), 310–328). Proof: OpenAI, Exponential decay in two-dimensional classical O(n) models, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 215, commit adc7f12, Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/ClassicalON/IsingGinibre.lean (OpenAI's theorem OAI.ClassicalON.ising_edge_covariance_nonneg)

import Mathlib
import Definitions.Def_OAIQWCO001

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uE uV

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace ClassicalON

variable {V : Type uV} {E : Type uE} [Fintype V] [Fintype E]

theorem ising_edge_covariance_nonneg (left right : E → V) (b : E → ℝ)
    (hb : ∀ e,0≤b e) (e f : E) :
    isingMean left right b (isingEnergy left right e)*
      isingMean left right b (isingEnergy left right f) ≤
    isingMean left right b (fun s => isingEnergy left right e s*isingEnergy left right f s) := by
  sorry

end ClassicalON

end

end OAI
end
