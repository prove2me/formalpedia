-- Prove2me | Theorems.Thm_MultistageStab_Value_display_11
-- name    : MultistageStab.Value.display_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T07:50:12.684613+00:00
-- url     : https://prove2.me/theorems/b6f63451-3c76-4a26-ade0-9de145eac3a6
-- title:
--   (11), proof of Theorem 2.1, pp. 5–6 — an adapted feasible x̃ with ‖E[x̄_t|F̃_t] − x̃_t‖ ≤ L_t(…)
-- statement:
--   Work in the setting of program (1) with a randomness pattern and its exponents $r, r'$. Let $\xi$ be an admissible input and assume complete fixed recourse (A1). Then there are constants $L_t > 0$ with the following property. For every admissible input $\tilde\xi$, with generated filtration $\tilde{\mathcal F}_t = \sigma(\tilde\xi_1,\dots,\tilde\xi_t)$, and every feasible policy $\bar x \in \mathcal X(\xi)$, there is a feasible policy $\tilde x \in \mathcal X(\tilde\xi)$ (so $\tilde x_t$ is $\tilde{\mathcal F}_t$-measurable, in $L_{r'}$, $\tilde x_t \in X_t$, and $A_{t,0}\tilde x_t + A_{t,1}\tilde x_{t-1} = h_t(\tilde\xi_t)$) with $\tilde x_1 = \bar x_1$ and, almost surely for every $t = 2,\dots,T$,
--   $$\big\|\mathbb E[\bar x_t \mid \tilde{\mathcal F}_t] - \tilde x_t\big\| \le L_t\Big( \sum_{\tau=2}^{t} \mathbb E\big[\|\xi_\tau - \tilde\xi_\tau\| \,\big|\, \tilde{\mathcal F}_\tau\big] + \sum_{\tau=2}^{t-1} \mathbb E\big[\|\bar x_\tau - \mathbb E[\bar x_\tau \mid \tilde{\mathcal F}_\tau]\| \,\big|\, \tilde{\mathcal F}_{\tau+1}\big]\Big).$$
--   If only the costs are random, the first sum is absent.
--
--   The constants $L_t$ do not depend on $\tilde\xi$ or $\bar x$. This estimate transfers a policy that is adapted to the filtration of $\xi$ to one adapted to the filtration of $\tilde\xi$, and is the core of the stability proof.
--
--   **Formalization Note** The paper constructs $\tilde x$ for $\bar x$ in an $\varepsilon$-level set; the statement here takes any feasible $\bar x$, which the construction allows and which is stronger. The case "only costs random" is the pattern `costs`, in which the first sum is replaced by $0$.
-- source:
--   Heitsch, Römisch & Strugarek, Stability of multistage stochastic programs, author manuscript (edoc.hu-berlin.de, c. 2005), pp. 5–6, proof of Theorem 2.1, construction of x̃ and (11)

import Mathlib
import Definitions.Def_MultistageStab_Value_Setting

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace MultistageStab.Value

theorem display_11 (D : Data) (pat : Pattern) (hpat : pat.Holds D)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ξ : ℕ → Ω → E D.d) (hA1 : CompleteRecourse D) (hA3 : Admissible P D pat ξ) :
    ∃ L : ℕ → ℝ, (∀ t, 0 < L t) ∧
      ∀ ξ' : ℕ → Ω → E D.d, Admissible P D pat ξ' →
        ∀ xbar ∈ feasible P D pat ξ, ∃ xtil ∈ feasible P D pat ξ', xtil 1 = xbar 1 ∧
          ∀ t ∈ Finset.Icc 2 D.T, ∀ᵐ ω ∂P,
            ‖P[xbar t | sigmaGen ξ' t] ω - xtil t ω‖ ≤
              L t * ((if pat = Pattern.costs then 0 else
                  ∑ τ ∈ Finset.Icc 2 t,
                    P[fun ω => ‖ξ τ ω - ξ' τ ω‖ | sigmaGen ξ' τ] ω) +
                ∑ τ ∈ Finset.Icc 2 (t - 1),
                  P[fun ω => ‖xbar τ ω - P[xbar τ | sigmaGen ξ' τ] ω‖ | sigmaGen ξ' (τ + 1)] ω) := by sorry

end MultistageStab.Value
