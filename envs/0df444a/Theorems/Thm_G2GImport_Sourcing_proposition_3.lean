-- Prove2me | Theorems.Thm_G2GImport_Sourcing_proposition_3
-- name    : G2GImport.Sourcing.proposition_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:12:52.20663+00:00
-- url     : https://prove2.me/theorems/3f276bc7-c6c7-49e1-b50c-5c1f89767563
-- title:
--   Proposition 3: more suppliers favor the buyer; forward eventually beats ad hoc
-- statement:
--   A buyer with unit demand and internal yield uniform on $[0,1]$ bargains with $l\ge1$ identical suppliers of cost $c$, with buyer bargaining power $\gamma$. Assume $0<\gamma<1$ and $0<c<1-\gamma$. Compare the symmetric equilibrium of $l$ ad hoc suppliers with that of $l$ forward suppliers, each regime having no suppliers of the other type. Such equilibria exist for every $l\ge1$.
--
--   In either regime, moving from $l$ to $l+1$ suppliers strictly raises the buyer's expected net utility and strictly lowers the suppliers' **total** profit, $lU_S^*$. Moreover, some positive threshold $L$ exists such that for every integer $l>L$,
--   $$U_B^{f*}(l)>U_B^{a*}(l).$$
--   These comparisons hold for every symmetric equilibrium of the defined Nash-in-Nash games. The result explains why forward contracts become better for the buyer as the supplier pool grows.
--
--   **Formalization Note** The theorem includes existence to prevent vacuous equilibrium comparisons. The strict cost bound excludes the equality case $c=1-\gamma$, where ad hoc monotonicity ceases to be strict. The integer threshold is equivalent to the paper's real threshold for integer supplier counts.
-- source:
--   Mu, Hu, Reddy & Gavirneni, Negotiating government-to-government food importing contracts: a Nash bargaining framework, accepted manuscript (MSOM, doi:10.1287/msom.2021.1027), PDF p. 9, Proposition 3

import Mathlib
import Definitions.Def_G2GImport_Sourcing_Model

namespace G2GImport.Sourcing

/-- Proposition 3: additional symmetric suppliers benefit the buyer and reduce
total supplier profit, and forward contracting eventually benefits the buyer more. -/
theorem proposition_3 (P : Params) (hS : P.Standing) :
    (∀ l : ℕ, 1 ≤ l →
      (∃ k q t, IsAdHocEq P l k q t) ∧
      ∃ q t, IsForwardEq P l q t) ∧
    (∀ l : ℕ, 1 ≤ l → ∀ k q t k' q' t',
      IsAdHocEq P l k q t → IsAdHocEq P (l + 1) k' q' t' →
      adHocBuyer l q t < adHocBuyer (l + 1) q' t' ∧
      ((l : ℝ) + 1) * adHocSupplier P k' t' <
        (l : ℝ) * adHocSupplier P k t) ∧
    (∀ l : ℕ, 1 ≤ l → ∀ q t q' t',
      IsForwardEq P l q t → IsForwardEq P (l + 1) q' t' →
      fwdBuyer l q t < fwdBuyer (l + 1) q' t' ∧
      ((l : ℝ) + 1) * fwdSupplier P q' t' <
        (l : ℝ) * fwdSupplier P q t) ∧
    (∃ L : ℕ, 0 < L ∧ ∀ l : ℕ, L < l → ∀ k q t qf tf,
      IsAdHocEq P l k q t → IsForwardEq P l qf tf →
        adHocBuyer l q t < fwdBuyer l qf tf) := by sorry

end G2GImport.Sourcing
