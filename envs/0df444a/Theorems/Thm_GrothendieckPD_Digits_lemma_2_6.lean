-- Prove2me | Theorems.Thm_GrothendieckPD_Digits_lemma_2_6
-- name    : GrothendieckPD.Digits.lemma_2_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T21:06:14.767904+00:00
-- url     : https://prove2.me/theorems/eca3ba6e-cc12-4c75-92c2-076197a2d2a2
-- title:
--   Lemma 2.6: odd optimizers suffice for $\mathrm{OPT}(Q)$, $q\in\mathcal Q$
-- statement:
--   Let $q\in\mathcal Q$ (so $q_1=1$, $|q_m|\le1$, $q_{2m}=0$) and $Q=\sum_{\text{odd }m\ge1}q_m\Pi_m$ on $L^2(\gamma_n)$, $n\ge1$. Then
--   $$\mathrm{OPT}(Q)=\sup_{f,g:\mathbb R^n\to\{\pm1\}}\langle f,Qg\rangle=\sup_{\text{odd }f,g:\mathbb R^n\to\{\pm1\}}\langle f,Qg\rangle,$$
--   where $\langle f,Qg\rangle=\sum_mq_mc_m(f,g)$. In the formal statement both suprema are asserted to be least upper bounds equal to $v_n(q)$.
--
--   The lemma lets the duality theory restrict to odd rounding functions.
--
--   Differences from the source:
--   - reading: odd functions f, g : ℝⁿ → {±1} → f(−x) = −f(x) for γₙ-almost every x; reason: pointwise oddness is impossible for ±1-valued functions (f(0) = −f(0)); a.e. oddness is the only satisfiable meaning and every Hermite coefficient depends only on the a.e. class
--   - encoding: f, g : ℝⁿ → {±1} → measurable functions with values in {1, −1} (GrothendieckLB.IsSignFn); reason: Hermite coefficients require measurability; the source states it in Lemma 2.5 and uses it throughout
--   - encoding: c_m(f, g) = ⟨Π_m f, Π_m g⟩ → the moment sum ∑_{|α| = m} E[f He_α] E[g He_α] / α! (GrothendieckLB.pmInner); reason: same value by orthonormality of ψ_α = He_α/√α!
--   - reading: ℝⁿ, n ∈ ℕ → n ≥ 1; reason: ℝ⁰ is a point carrying no odd ±1-valued function, so the odd supremum would be over the empty set; the proof uses a(X) = sign(X₁)
--   - encoding: Q = ∑_{odd m ≥ 1} q_m Π_m → payoff ∑_{m ≥ 0} q_m c_m(f,g); reason: q_{2m} = 0 for q ∈ 𝒬, so the even terms vanish
--   - encoding: equalities of suprema → IsLUB of each set at v_n(q); reason: records that both suprema are finite and equal to OPT(Q) = v_n(q); avoids Lean's sSup default
-- source:
--   Steven Heilman, Chris Jones, Giulio Malavolta, Primal/Dual Method for the Grothendieck Constant, STOC 2027 submission #820 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/820.pdf, Lemma 2.6, p. 5

import Mathlib
import Definitions.Def_GrothendieckPD_Digits_FiniteGames

namespace GrothendieckPD.Digits

/-- Lemma 2.6 (p. 5). For `q ∈ 𝒬` and `Q = ∑_{odd m ≥ 1} q_m Π_m` on `L²(γ_n)`, `n ≥ 1`,
`OPT(Q) = sup_{f,g : ℝ^n → {±1}} ⟨f, Qg⟩ = sup_{odd f,g : ℝ^n → {±1}} ⟨f, Qg⟩`; both sets have
least upper bound `v_n(q)` (no maximizing pair is asserted). -/
theorem lemma_2_6 (q : ℕ → ℝ) (hq : q ∈ QSet) (n : ℕ) (hn : 1 ≤ n) :
    IsLUB {s : ℝ | ∃ f g : (Fin n → ℝ) → ℝ, GrothendieckLB.IsSignFn f ∧
        GrothendieckLB.IsSignFn g ∧ s = gamePayoff q f g} (gameValue n q) ∧
    IsLUB {s : ℝ | ∃ f g : (Fin n → ℝ) → ℝ, GrothendieckLB.IsSignFn f ∧
        GrothendieckLB.IsSignFn g ∧ IsOddAE f ∧ IsOddAE g ∧ s = gamePayoff q f g}
      (gameValue n q) := by sorry

end GrothendieckPD.Digits
