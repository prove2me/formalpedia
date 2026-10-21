-- Prove2me | Theorems.Thm_G2GImport_Sourcing_lemma_2
-- name    : G2GImport.Sourcing.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:12:53.061618+00:00
-- url     : https://prove2.me/theorems/42f4bd4c-d85e-45c1-adbb-4f64020b82e2
-- title:
--   Lemma 2: single-supplier forward quantity, payment, and payoffs
-- statement:
--   For one forward supplier with production cost $c$ and buyer bargaining power $\gamma$ in the positive-production regime, the contracted and produced quantity is $q^{f*}=k^{f*}=1-\sqrt c$. The payment is
--   $$t^{f*}=\frac{3c\gamma-\gamma+1-(2\gamma+1)c^{3/2}}{3}.$$
--   The buyer's expected net utility is $U_B^{f*}=(2c^{3/2}\gamma-3c\gamma+\gamma+2)/3$, and the supplier's profit is $U_S^{f*}=(1-\sqrt c)(\sqrt c+1-2c)(1-\gamma)/3$.
--
--   This benchmark makes the single-supplier forward and ad hoc outcomes directly comparable.
--
--   **Formalization Note** Forward production equals the contracted quantity as assumed in §4.1.
-- source:
--   Mu, Hu, Reddy & Gavirneni, Negotiating government-to-government food importing contracts: a Nash bargaining framework, accepted manuscript (MSOM, doi:10.1287/msom.2021.1027), PDF p. 6, Lemma 2

import Mathlib
import Definitions.Def_G2GImport_Sourcing_Model

namespace G2GImport.Sourcing

/-- Lemma 2: the single-supplier forward quantity, payment, and payoffs. -/
theorem lemma_2 (P : Params) (hS : P.Standing) (q t : ℝ)
    (heq : IsForwardEq P 1 q t) :
    q = 1 - Real.sqrt P.c ∧
    t = (3 * P.c * P.γ - P.γ + 1 -
      (2 * P.γ + 1) * P.c ^ ((3 : ℝ) / 2)) / 3 ∧
    fwdBuyer 1 q t =
      (2 * P.c ^ ((3 : ℝ) / 2) * P.γ - 3 * P.c * P.γ + P.γ + 2) / 3 ∧
    fwdSupplier P q t =
      (1 - Real.sqrt P.c) * (Real.sqrt P.c + 1 - 2 * P.c) * (1 - P.γ) / 3 := by sorry

end G2GImport.Sourcing
