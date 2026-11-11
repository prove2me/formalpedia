-- Prove2me | Theorems.Thm_GlobalUpdatesFO_Upper_lemma_4_25
-- name    : GlobalUpdatesFO.Upper.lemma_4_25
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T07:22:30.077023+00:00
-- url     : https://prove2.me/theorems/566a7ffc-3461-4fd5-a126-76c2c8094d8d
-- title:
--   Lemma 4.25 — an interpretation followed by restriction to an FO^q-definable set does not increase µ_q, and strictly decreases it when the set is proper
-- statement:
--   Let $q \ge 1$, $A$ a $\Sigma$-structure, $I$ a $q$-bounded $(\Sigma,\Pi)$-interpretation and $\delta(x) \in \mathrm{FO}^q[\Sigma]$ a unary formula, and let $X = \{v \in U(A) : A \models \delta(v)\}$. Then
--   $$\mu_q(I(A)[X]) \le \mu_q(A),$$
--   and the inequality is strict if $X \ne U(A)$.
--
--   The first-order index is the potential of the paper's amortized analysis; this lemma says global updates and definable restrictions never increase it.
--
--   Differences from the source:
--   - encoding: µ_q(B) = min |U(B′)| over finite structures B′ ≡_q B → foIndex q B = sInf {m | ∃ B′ : Structure _ (Fin m), tp0 q B′ = tp0 q B}; reason: every finite structure is isomorphic to one on Fin m and full types are isomorphism invariant; the set contains |U(B)| so the infimum is a minimum
--   - encoding: a finite Σ-structure with universe U(A), relation names of Σ with their arities → Structure σ U on a finite type U : Type, Σ the list of arities, relation names 0, …, |Σ|−1; reason: Lean convention; every finite structure is of this form up to renaming
--   - encoding: formulas of FO^k[Σ] with r free variables x̄, up to renaming of bound variables → named-variable Formula over ℕ; IsFOk σ k r φ: WF, free variables among x_0, …, x_{r−1}, and |vars(φ) ∪ {0, …, r−1}| ≤ k; reason: the paper's definition (p. 17) with the free tuple fixed to x_0, …, x_{r−1}; renaming bound variables changes no type
-- source:
--   Korhonen, Sokołowski, On efficient global updates in first-order logic, STOC 2027 submission (manuscript sha256 ffb1e749…), p. 41, Lemma 4.25

import Mathlib
import Definitions.Def_GlobalUpdatesFO_Upper_Structure
import Definitions.Def_GlobalUpdatesFO_Upper_Formula
import Definitions.Def_GlobalUpdatesFO_Upper_Flattening
import Definitions.Def_GlobalUpdatesFO_Upper_Robust

namespace GlobalUpdatesFO.Upper

theorem lemma_4_25 (σ π : Signature) (q : ℕ) (hq : 1 ≤ q) (U : Type) [Fintype U]
    (A : Structure σ U) (I : Interp σ π) (hI : I.IsKBounded q)
    (δ : Formula) (hδ : IsFOk σ q 1 δ) :
    foIndex q ((I.apply A).induced {v | Sat A δ ![v]}) ≤ foIndex q A ∧
      ({v | Sat A δ ![v]} ≠ Set.univ →
        foIndex q ((I.apply A).induced {v | Sat A δ ![v]}) < foIndex q A) := by sorry

end GlobalUpdatesFO.Upper
